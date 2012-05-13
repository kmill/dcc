{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

-- | We kind of follow "Iterated Register Coalescing" by Lal George
-- and Andrew Appel.
module RegAlloc.Allocator where 

import qualified Data.Map as M
import Assembly
import qualified Assembly as A
import AliveDead
import CodeGenerate
import qualified IR as I
import Dataflow
import Dataflow.DeadCodeAsm
import DataflowTypes
import qualified Data.Set as S
import Data.List
import Data.Int
import Control.Monad.State
import Compiler.Hoopl
import Data.Maybe
import AST (SourcePos, noPosition)
import Debug.Trace
import Data.Function
import Data.Either (lefts, rights)
import Util.NodeLocate
import qualified LoopAnalysis as L
import RegAlloc.InterfGraph
import qualified Dataflow.GenWebs as GenWebs
import Dataflow.OptSupport (joinProd, joinSets, setLattice, (><))

dotrace = False

trace' a b = if dotrace then trace a b else b 

-- | Main entry point to allocating registers for the IR
regAlloc :: LowIRRepr -> I.GM LowIRRepr
regAlloc lir
    = do LowIRRepr fields strs meths graph <- evalStupidFuelMonad (performDeadAsmPass lir) maxBound
         let GMany _ body _ = graph
             mlabels = map I.methodEntry meths
         massgraph <- evalStupidFuelMonad (massageGraph mlabels graph) maxBound
         --graph' <- error $ I.graphToGraphViz show massgraph
         let graph' = foldl1 (|*><*|) $ map (\mlabel -> doRegAlloc freeSpillLocs mlabel (subgraph massgraph mlabel)) mlabels
         graph'' <- evalStupidFuelMonad (collectSpill mlabels graph') maxBound
         let lir' = LowIRRepr fields strs meths graph''
         evalStupidFuelMonad (performDeadAsmPass lir') maxBound
    where
      subgraph :: Graph A.Asm C C -> Label -> Graph A.Asm C C
      subgraph (GMany _ body _) label = let blocks = postorder_dfs_from body label
                                        in foldl1 (|*><*|) (map blockGraph blocks)


-- | Collects and rewrites the spills in the graph to moves.
collectSpill :: [Label] -> Graph A.Asm C C -> RM (Graph A.Asm C C)
collectSpill mlabels graph
    = do let pg = toPGraph graph
             spillWebs = GenWebs.getWebs spillAliveDead mlabels pg
             spillTable = GenWebs.makeTables spillWebs
--             spillInterf = GenWebs.makeInterfGraph mlabels pg spillWebs
         (_, smvs, _) <- analyzeAndRewriteBwd
                         (collectSpillMovePass spillTable)
                         (JustC mlabels)
                         pg
                         mapEmpty
         let spillMoves = M.unions $ map (\l -> fst $ fromJust $ lookupFact l smvs) mlabels
             spillInterf = GenWebs.makeInterfGraph mlabels pg spillWebs spillMoves
             colors = combineSpills spillInterf spillMoves
             graph' = mapGraph (renameSpills colors spillInterf) pg
         (graph'', _, _) <- analyzeAndRewriteFwd
                            betterifySpills
                            (JustC mlabels)
                            graph'
                            (mapFromList (map (\l -> (l, fact_bot betterifyLattice)) mlabels))
         (_, f, _) <- analyzeAndRewriteBwd
                      collectSpillPass
                      (JustC mlabels)
                      graph''
                      mapEmpty
         (g, _, _) <- analyzeAndRewriteFwd
                      (rewriteSpillPass f)
                      (JustC mlabels)
                      graph''
                      f
         return g

renameSpills :: forall e x. M.Map WebID SpillLoc -> GenWebs.InterfGraph SpillLoc 
             -> PNode A.Asm e x -> A.Asm e x
renameSpills colors igraph (PNode l n)
    = case n of
        A.Spill pos r s -> A.Spill pos r (getColorDef s)
        A.Reload pos s r -> A.Reload pos (getColorUse s) r
        n' -> n'
      where getColorUse s = colors M.! GenWebs.lookupVarUse s l (GenWebs.igWebTable igraph)
            getColorDef s = colors M.! GenWebs.lookupVarDef s l (GenWebs.igWebTable igraph)
             

spillAliveDead :: forall e x. A.Asm e x -> ([SpillLoc], [SpillLoc])
spillAliveDead (A.Enter _ _ args _) = if args > 6
                                      then ([], lefts $ drop 6 (take args A.argLocation))
                                      else ([], [])
spillAliveDead (A.Spill _ _ s) = ([], [s])
spillAliveDead (A.Reload _ s _) = ([s], [])
spillAliveDead _ = ([], [])

-- | Gets the list of spills for each entry point. TODO: make it also
-- find live ranges for spills so we can reuse stack space.
collectSpillPass :: (CheckpointMonad m, FuelMonad m)
                    => BwdPass m A.Asm (S.Set SpillLoc)
collectSpillPass = BwdPass
                   { bp_lattice = setLattice
                   , bp_transfer = getSpillTransfer
                   , bp_rewrite = noBwdRewrite }
    where
      getSpillTransfer :: BwdTransfer A.Asm (S.Set SpillLoc)
      getSpillTransfer = mkBTransfer3 usedCO usedOO usedOC
          where
            usedCO :: A.Asm C O -> (S.Set SpillLoc) -> (S.Set SpillLoc)
            usedCO _ f = f

            usedOO :: A.Asm O O -> (S.Set SpillLoc) -> (S.Set SpillLoc)
            usedOO (A.Spill _ _ s) f = S.insert s f
            usedOO (A.Reload _ s _) f = S.insert s f
            usedOO _ f = f

            usedOC :: A.Asm O C -> FactBase (S.Set SpillLoc) -> (S.Set SpillLoc)
            usedOC x f = S.unions $ map
                         ((fromMaybe S.empty) . (flip lookupFact f))
                         (successors x)

-- This is of (moves, tomove)
type CollectSpillMoveFact = (M.Map NodePtr (S.Set WebID, S.Set WebID),
                             M.Map Reg (S.Set WebID))

-- | Collects a list of "spill moves"
collectSpillMovePass :: (CheckpointMonad m, FuelMonad m)
                        => GenWebs.WebTables SpillLoc
                        -> BwdPass m (PNode A.Asm) CollectSpillMoveFact
collectSpillMovePass spills
    = BwdPass
      { bp_lattice = getSpillMoveLattice
      , bp_transfer = getSpillMoveTransfer
      , bp_rewrite = noBwdRewrite }
    where
      getSpillMoveLattice :: DataflowLattice CollectSpillMoveFact
      getSpillMoveLattice = DataflowLattice
                            { fact_name = "Spill move lattice"
                            , fact_bot = (M.empty, M.empty)
                            , fact_join = joinProd (joinMaps (joinProd joinSets joinSets))
                                          (joinMaps joinSets) }
      getSpillMoveTransfer :: BwdTransfer (PNode A.Asm) CollectSpillMoveFact
      getSpillMoveTransfer = mkBTransfer3 usedCO usedOO usedOC
          where
            usedCO :: (PNode A.Asm) C O -> CollectSpillMoveFact -> CollectSpillMoveFact
            usedCO (PNode _ n) (moves, tomove) = (moves, remove dead tomove)
                where (_, dead) = getAliveDead n
            
            usedOO :: (PNode A.Asm) O O -> CollectSpillMoveFact -> CollectSpillMoveFact
            usedOO (PNode l (A.Reload _ s r)) (moves, tomove)
                = case M.lookup r tomove of
                    Just webs -> (moves', M.delete r tomove)
                        where spillID = GenWebs.lookupVarUse s l spills
                              moves' = M.insertWith update l
                                       (S.singleton spillID, webs)
                                       moves
                              update = S.union >< S.union
                    Nothing -> (moves, tomove)
            usedOO (PNode l (A.Spill _ r s)) (moves, tomove)
                = (moves, tomove')
                  where tomove' = M.insertWith S.union r (S.singleton spillID) tomove
                        spillID = GenWebs.lookupVarDef s l spills
            usedOO (PNode l n) (moves, tomove)
                = (moves, remove dead tomove)
                  where (_, dead) = getAliveDead n
            
            usedOC :: (PNode A.Asm) O C -> FactBase CollectSpillMoveFact -> CollectSpillMoveFact
            usedOC (PNode l n) fs = (moves, remove dead tomove)
                where (moves, tomove) = joinOutFacts getSpillMoveLattice n fs
                      (_, dead) = getAliveDead n
            
            remove :: Ord k => [k] -> M.Map k v -> M.Map k v
            remove items m = foldl (flip id) m (map M.delete items)

data SpillWorklists = SpillWorklists
    { swAliases :: M.Map WebID WebID
    , swMoves :: [(NodePtr, WebID, WebID)]
    , swWebs :: [WebID]
    , swColors :: M.Map WebID SpillLoc
    , swInterfGraph :: GenWebs.InterfGraph SpillLoc
    }
    deriving Show

swGetAlias :: WebID -> SpillWorklists -> WebID
swGetAlias i sw = case M.lookup i (swAliases sw) of
                    Just i' -> swGetAlias i' sw
                    Nothing -> i

-- | Main entry point for spill recoloring
combineSpills :: GenWebs.InterfGraph SpillLoc
              -> M.Map NodePtr (S.Set WebID, S.Set WebID)
              -> M.Map WebID SpillLoc
combineSpills graph moves
    = let sw = makeSpillWorklists graph moves
          sw' = mergeSpills sw
          sw'' = colorSpills sw'
      in swColors sw''
    where
      makeSpillWorklists :: GenWebs.InterfGraph SpillLoc
                         -> M.Map NodePtr (S.Set WebID, S.Set WebID)
                         -> SpillWorklists
      makeSpillWorklists graph moves
          = SpillWorklists
            { swAliases = M.empty
            , swMoves = do (l, (srcs, dests)) <- M.toList moves
                           s <- S.toList srcs
                           d <- S.toList dests
                           return (l, s, d)
            , swWebs = GenWebs.igGetWebIDs graph
            , swColors = M.empty
            , swInterfGraph = graph
            }

      addAlias :: WebID -> WebID -> SpillWorklists -> SpillWorklists
      addAlias u v sw
          = sw { swAliases = M.insert v u $ swAliases sw
               , swWebs = delete v $ swWebs sw
               , swInterfGraph = GenWebs.igMergeWebs u v $ swInterfGraph sw }

      mergeSpills :: SpillWorklists -> SpillWorklists
      mergeSpills sw
          = case swMoves sw of
              [] -> sw
              (l,s,d):mvs
                  | u == v -> mergeSpills sw'
                  | fixedWeb vweb || interferes -> mergeSpills sw'
                  | otherwise -> mergeSpills (addAlias u v sw')
                  where s' = swGetAlias s sw
                        d' = swGetAlias d sw
                        dweb = GenWebs.igGetWeb d' (swInterfGraph sw)
                        (u, v) = if fixedWeb dweb then (d', s') else (s', d')
                        vweb = GenWebs.igGetWeb v (swInterfGraph sw)
                        interferes = GenWebs.igInterferes u v (swInterfGraph sw)
                  
                        sw' = sw { swMoves = mvs }
                  
      fixedWeb web = case GenWebs.webVar web of
                       SpillID _ -> False
                       SpillSID _ -> False
                       SpillArg _ -> True

      colorSpills :: SpillWorklists -> SpillWorklists
      colorSpills sw
          = let sw' = emptyStack (swWebs sw) sw
                getAliasColor i = swColors sw' M.! swGetAlias i sw'
                webids = GenWebs.igGetWebIDs (swInterfGraph sw')
            in sw' { swColors = M.fromList $ map (\i -> (i, getAliasColor i)) $ webids }
          where emptyStack [] sw = sw
                emptyStack (i:is) sw
                    | fixedWeb web
                        = let sw' = sw { swColors = M.insert i (GenWebs.webVar web) $ swColors sw }
                          in emptyStack is sw'
                    | otherwise
                        = let adj = filter (`elem` swWebs sw) $
                                    S.toList $ GenWebs.igGetAdj i (swInterfGraph sw)
                              neighcolors = catMaybes $ map (`M.lookup` swColors sw') adj
                              okColors = A.freeSpillLocs \\ neighcolors
                              sw' = sw { swColors = M.insert i (head okColors) $ swColors sw }
                          in emptyStack is sw'
                    where web = GenWebs.igGetWeb i (swInterfGraph sw)

data BetterifyLoc = BInt64 Int64
                  | BSpill SpillLoc
                  | BReg Reg
                    deriving (Eq, Ord, Show)
type BetterifyFact = ( M.Map SpillLoc (WithTop BetterifyLoc)
                     , M.Map Reg (WithTop BetterifyLoc))

betterifyLattice :: DataflowLattice BetterifyFact
betterifyLattice = DataflowLattice
                   { fact_name = "betterify lattice"
                   , fact_bot = (M.empty, M.empty)
                   , fact_join = joinProd
                                 (joinMaps (extendJoinDomain add))
                                 (joinMaps (extendJoinDomain add)) }
    where add _ (OldFact bl1) (NewFact bl2)
              = if bl1 == bl2
                then (NoChange, PElem bl1)
                else (SomeChange, Top)

betterifySpills :: forall m. (CheckpointMonad m, FuelMonad m) =>
                   FwdPass m Asm BetterifyFact
betterifySpills = FwdPass
                  { fp_lattice = betterifyLattice
                  , fp_transfer = bTransfer
                  , fp_rewrite = rewrite }
    where 
          
          bTransfer = mkFTransfer3 ftCO ftOO ftOC
          ftCO :: Asm C O -> BetterifyFact -> BetterifyFact
          ftCO (Enter _ _ numargs _) (spills, regs)
              = (spills'', regs')
                where spills' = M.fromList $ map (\a -> (a, Top)) $ 
                                lefts $ drop 6 $ take numargs A.argLocation
                      spills'' = if numargs > 6 then spills' else M.empty
                      regs' = M.fromList $ map (\a -> (a, Top)) $
                              rights $ take (min 6 numargs) A.argLocation
          ftCO _ f = f
          
          removeBindingsTo :: Ord k => BetterifyLoc -> M.Map k (WithTop BetterifyLoc)
                           -> M.Map k (WithTop BetterifyLoc)
          removeBindingsTo x oldMap = newMap
              where newMap = M.mapMaybe f oldMap
                    f p@(PElem v) = if v == x then Nothing else Just p
                    f y = Just y
          
          lookupBInt64 :: BetterifyLoc -> BetterifyFact -> BetterifyLoc
          lookupBInt64 v (spills, regs)
              = case v of
                  BReg r -> case M.lookup r regs of
                              Just (PElem (BInt64 i)) -> BInt64 i
                              _ -> BReg r
                  BSpill l -> case M.lookup l spills of
                                Just (PElem (BInt64 i)) -> BInt64 i
                                _ -> BSpill l
                  _ -> v
          
          handleToR :: BetterifyLoc -> Reg -> BetterifyFact -> BetterifyFact
          handleToR v r (spills, regs)
              = ( removeBindingsTo (BReg r) spills
                , M.insert r (PElem v') $ removeBindingsTo (BReg r) regs )
              where v' = lookupBInt64 v (spills, regs)
                           
          handleToS :: BetterifyLoc -> SpillLoc -> BetterifyFact -> BetterifyFact
          handleToS v s (spills, regs)
              = ( M.insert s (PElem v') $ removeBindingsTo (BSpill s) spills
                , removeBindingsTo (BSpill s) regs )
              where v' = lookupBInt64 v (spills, regs)
          
          removeToR :: Reg -> BetterifyFact -> BetterifyFact
          removeToR r (spills, regs)
              = ( removeBindingsTo (BReg r) spills
                , M.insert r Top $ removeBindingsTo (BReg r) regs )
          
          ftOO :: Asm O O -> BetterifyFact -> BetterifyFact
          ftOO (Spill _ r s) f = handleToS (BReg r) s f
          ftOO (Reload _ s r) f = handleToR (BSpill s) r f
          ftOO (MovIRMtoR _ (IRM_I (Imm32 i)) r) f = handleToR (BInt64 $ fromIntegral i) r f
          ftOO (MovIRMtoR _ (IRM_R r0) r) f = handleToR (BReg r0) r f
          ftOO (Mov64toR _ (Imm64 i) r) f = handleToR (BInt64 i) r f
          ftOO n f = let (alive, dead) = getAliveDead n
                     in foldl (flip id) f (map removeToR dead)
          
          ftOC :: Asm O C -> BetterifyFact -> FactBase BetterifyFact
          ftOC = distributeFact
          
          rewrite :: FwdRewrite m Asm BetterifyFact
          rewrite = deepFwdRw3 rwCO rwOO rwOC
          
          rwCO :: Asm C O -> BetterifyFact -> m (Maybe (Graph Asm C O))
          rwCO n f = return Nothing
          
          getR :: Reg -> BetterifyFact -> Maybe BetterifyLoc
          getR r (spills, regs) = case M.lookup r regs of
                                    Just (PElem v) -> Just v
                                    _ -> Nothing
          
          getS :: SpillLoc -> BetterifyFact -> Maybe BetterifyLoc
          getS s (spills, regs) = case M.lookup s spills of
                                    Just (PElem v) -> Just v
                                    _ -> Nothing
          
          rwOO :: Asm O O -> BetterifyFact -> m (Maybe (Graph Asm O O))
          rwOO (Spill pos r s) f
              = return $ case getR r f of
                           Just (BReg r') -> Just $ mkMiddle $ Spill pos r' s
                           Just (BSpill s') | s == s' -> Just emptyGraph
                           _ -> Nothing
          rwOO (Reload pos s r) f
              = return $ case getS s f of
                           Just (BReg r') -> Just $ mkMiddle $ mov pos r' r
                           Just (BInt64 i) -> Just $ mkMiddle $ mov pos i r
                           Just (BSpill s')
                               | s /= s' -> Just $mkMiddle $ Reload pos s' r
                           _ -> Nothing
          rwOO (MovIRMtoR pos (IRM_R r0) r) f
              = return $ case getR r0 f of
                           Just (BReg r0') | r0' /= r0 -> Just $ mkMiddle $ mov pos r0' r
                           Just (BInt64 i) -> Just $ mkMiddle $ mov pos i r
                           _ -> Nothing
          rwOO n f = return $ mkMiddle `fmap` mapAsm rename (const Nothing) n
              where pinned = getPinned n
                    rename r
                        | r `elem` pinned  = Nothing
                        | otherwise
                          = case getR r f of
                              Just (BReg r') | r == r' -> Nothing
                                             | otherwise -> Just r'
                              _ -> Nothing
          
          rwOC :: Asm O C -> BetterifyFact -> m (Maybe (Graph Asm O C))
          rwOC n f = return Nothing

-- | Rewrites the spills to moves.
rewriteSpillPass :: (CheckpointMonad m, FuelMonad m) =>
                    FactBase (S.Set SpillLoc) -> FwdPass m Asm (S.Set SpillLoc)
rewriteSpillPass fb = FwdPass 
                      { fp_lattice = rwLattice
                      , fp_transfer = sTransfer
                      , fp_rewrite = rewriteSpill }
    where rwLattice :: DataflowLattice (S.Set SpillLoc)
          rwLattice = setLattice
          
          sTransfer :: FwdTransfer Asm (S.Set SpillLoc)
          sTransfer = mkFTransfer3 g g' g''
              where 
                g :: Asm C O -> S.Set SpillLoc -> S.Set SpillLoc
                g (Enter p l _ _) _ = fromMaybe S.empty (lookupFact l fb)
                g e f = f
                g' e f = f
                g'' e f = mkFactBase rwLattice $ zip (successors e) (repeat f)

          rewriteSpill :: forall m. FuelMonad m => FwdRewrite m Asm (S.Set SpillLoc)
          rewriteSpill = mkFRewrite d
              where 
                d :: Asm e x -> S.Set SpillLoc -> m (Maybe (Graph Asm e x))
                d (A.Spill pos reg s) f
                    = return $ Just $ mkMiddle $ A.mov pos reg (toMem s f)
                d (A.Reload pos s reg) f
                    = return $ Just $ mkMiddle $ A.mov pos (toMem s f) reg
                d (A.Enter pos l n x) f = if x' == x
                                          then return Nothing
                                          else return $ Just $ mkFirst $
                                               A.Enter pos l n x'
                    where x' = countSpillID f
                d (A.Leave pos rets x) f = if x' == x
                                           then return Nothing
                                           else return $ Just $ mkLast $
                                                A.Leave pos rets x'
                    where x' = countSpillID f

                d _ f = return Nothing
                
                countSpillID f = toNearestSafeSP $ fromIntegral $ 8 * (length $ normalSpills f)
                normalSpills f = S.toList $ S.filter (\s -> case s of
                                                              SpillArg _ -> False
                                                              _ -> True) f

                toMem :: SpillLoc -> S.Set SpillLoc -> MemAddr
                toMem (SpillArg r) f = A.MemAddr (Just $ A.MReg A.RSP)
                                       (A.Imm32 $ 8*(fromIntegral r) + 8 + countSpillID f)
                                       Nothing A.SOne
                toMem sl f = A.MemAddr (Just $ A.MReg A.RSP)
                             (A.Imm32 $ fromIntegral (8 * fromJust (findIndex (==sl) $ normalSpills f)))
                             Nothing A.SOne
                
                toNearestSafeSP :: Int32 -> Int32
                toNearestSafeSP i = i + ((i+8) `rem` (8*2))


          
data RWorklists = RWorklists
    { wInterfGraph :: InterfGraph
      
      -- Every web is in exactly one of the following:
    , wSpillWorklist :: [WebID] -- ^ high-degree webs
    , wFreezeWorklist :: [WebID] -- ^ low-degree move-related webs
    , wSimplifyWorklist :: [WebID] -- ^ list of low-degree non-move-related webs
    , wSpilledWebs :: [WebID] -- ^ webs marked for spilling
    , wCoalescedWebs :: S.Set WebID -- ^ webs that have been coalesced
    , wColoredWebs :: M.Map WebID X86Reg -- ^ webs successfully colored
    , wPrecoloredWebs :: S.Set WebID -- ^ webs which are precolored
                                     -- and shouldn't be spilled
    , wSelectStack :: [WebID] -- ^ stack containing temporaries
      
    , wCoalescedAlias :: M.Map WebID WebID -- ^ when (u,v) coalesced and v
                                           -- is in coalesced webs, then
                                           -- wCoalescedAlias[v]==u
    , wHaveSpilled :: Bool -- ^ whether a spill has been selected yet
    , wPreSpillCoalesced :: S.Set WebID -- ^ webs that have been coalesced before the first spill
    , wPreSpillAlias :: M.Map WebID WebID
    , wPreSpillCoalescedMoves :: S.Set MovePtr
      
    , wDegrees :: M.Map WebID Int -- ^ web to degree mapping.  fixed
                                  -- registers have maxBound degree
    , wSpillCosts :: M.Map WebID Int -- ^ web to spill cost mapping.
      
      -- Every move is in exactly one of the following
    , wWorklistMoves :: S.Set MovePtr -- ^ moves enabled for possible coalescing
    , wCoalescedMoves :: [MovePtr] -- ^ moves that have been coalesced
    , wConstrainedMoves :: [MovePtr] -- ^ moves whose source and target interfere
    , wFrozenMoves :: [MovePtr] -- ^ moves that will no longer be considered for coalescing
    , wActiveMoves :: S.Set MovePtr -- ^ moves not yet ready for coalescing
      
    , wMoves :: M.Map MovePtr [WebID] -- ^ a map from move nodes to web ids
    , wIdealRegs :: M.Map WebID [X86Reg] -- ^ a map from webs to fixed
                                         -- registers from associated moves
    , wLoops ::M.Map Label Int -- ^ a map from labels to the nesting of the loop
    }
                  deriving Show

displayWL :: RWorklists -> String
displayWL wl = unlines
               [ "Interference graph:"
               , dispIG (wInterfGraph wl)
               , "Simplify:"
               , show $ map dispWebName $ wSimplifyWorklist wl
               , "Freeze:"
               , show $ map dispWebName $ wFreezeWorklist wl
               , "Spill:"
               , show $ map dispWebName $ wSpillWorklist wl
               , "Coalesced:"
               , intercalate ", " $ map (\(a,b) -> "(" ++ dispWebName a ++ ", " ++ dispWebName b ++ ")") $ M.toList $ wCoalescedAlias wl
               , "Spilled:"
               , show $ map dispWebName $ wSpilledWebs wl
               , "Colored:"
               , intercalate ", " $ map (\(a,b) -> "(" ++ dispWebName a ++ ", " ++ show b ++ ")") $ M.toList $ wColoredWebs wl
               , "Degrees:"
               , intercalate ", " $ map (\(a,b) -> "(" ++ dispWebName a ++ ", " ++ show b ++ ")") $ M.toList $ wDegrees wl
               , "Worklist moves:"
               , show $ S.toList $ wWorklistMoves wl
               , "Coalesced moves:"
               , show $ wCoalescedMoves wl
               , "Constrained moves:"
               , show $ wConstrainedMoves wl
               , "Frozen moves:"
               , show $ wFrozenMoves wl
               , "Active moves:"
               , show $ S.toList $ wActiveMoves wl
               ]
    where dispIG g = unlines $ map showAdj (igWebIDs g)
              where dispWeb i = show i ++ "." ++ show (webReg web) ++ " " ++ pc
                                ++ "\n    d:" ++ show (S.toList $ webDefs web) ++ "\n    u:" ++ show (S.toList $ webUses web)
                                ++ "\n    m:" ++ show (S.toList $ webMoveNodes web)
                        where web = igGetWeb i g
                              pc = if webPrecolored web then "precolored" else ""
                    showAdj i = dispWeb i ++ arrayLike (map dispWebName $ S.toList $ igAdjLists g M.! i) ++ "\n"
                    arrayLike [] = ""
                    arrayLike lst = if length lst < 10
                                    then "\n   " ++ intercalate " " lst
                                    else "\n   " ++ intercalate " " (take 10 lst) ++ arrayLike (drop 10 lst)
          dispWebName i = show i ++ "." ++ show (webReg web)
              where web = igGetWeb i (wInterfGraph wl)

displayWL' wl = unlines
                [ "Simplify:"
                , show $ map dispWebName $ wSimplifyWorklist wl
                , "Freeze:"
                , show $ map dispWebName $ wFreezeWorklist wl
                , "Spill:"
                , show $ map dispWebName $ wSpillWorklist wl
                , "Select stack:"
                , show $ map dispWebName $ wSelectStack wl
                , "Coalesced:"
                , show $ map dispWebName $ S.toList $ wCoalescedWebs wl
                ]
    where dispWebName i = show i ++ "." ++ show (webReg web)
              where web = igGetWeb i (wInterfGraph wl)
                    
-- | Updates webMoveNodes to the given value for the web id
updateWebMoves' :: S.Set MovePtr -> WebID -> RWorklists -> RWorklists
updateWebMoves' s i wl
    = wl { wInterfGraph = g { igIDToWeb = M.insert i web' $ igIDToWeb g }}
    where g = wInterfGraph wl
          web = igIDToWeb g M.! i
          web' = web { webMoveNodes = s }
          
combineWebs :: WebID -> WebID -> RWorklists -> RWorklists
combineWebs i1 i2 wl
  = wl' { wSpillCosts = M.insert i1 (spillCost wl' i1) $ wSpillCosts wl' }
    where g = wInterfGraph wl
          web1 = igIDToWeb g M.! i1
          web2 = igIDToWeb g M.! i2
          web' = wUnion web1 web2
          wl' = wl { wInterfGraph = g { igIDToWeb = M.insert i1 web' $ igIDToWeb g } }

-- | Gets a web by id from the worklist.  Wrapper for 'igGetWeb'
wGetWeb :: WebID -> RWorklists -> Web
wGetWeb i wl = igGetWeb i (wInterfGraph wl)

-- | Gets the moves for a web by id from a worklist.  Wrapper for
-- webMoveNodes and wGetWeb.
getWebMoves' :: WebID -> RWorklists -> S.Set MovePtr
getWebMoves' i wl = webMoveNodes $ wGetWeb i wl

-- | Adds (u,v) to the adjacency lists if it's not already there,
-- updating the degrees appropriately.
addToAdjList :: WebID -> WebID -> AM ()
addToAdjList u v =
    do g <- gets wInterfGraph
       let adjs = igAdjLists g
       when (u /= v && not (v `S.member` (adjs M.! u))) $ do
         degrees <- gets wDegrees
         modify $ \wl -> wl { wInterfGraph = addInterfEdge u v g
                            , wDegrees = inc u $ inc v $ degrees }
    where inc i m = M.adjust (\d -> if d == maxBound then maxBound else d + 1) i m
         
-- | The allocator monad
type AM = State RWorklists

pushSelect :: WebID -> AM ()
pushSelect i = modify $ \wl -> wl { wSelectStack = i:(wSelectStack wl) }

popSelect :: AM WebID
popSelect =  do wl@(RWorklists { wSelectStack = (i:is) }) <- get
                put $ wl { wSelectStack = is }
                return i

isAdj :: WebID -> WebID -> RWorklists -> Bool
isAdj u v wl = S.member v $ (igAdjLists $ wInterfGraph wl) M.! u

-- | Takes a web id and gives the current list of adjacent web ids. "Adjacent"
adjacentWebs :: WebID -> AM (S.Set WebID)
adjacentWebs i =
  do g <- gets wInterfGraph
     select <- gets $ S.fromList . wSelectStack
     coalesced <- gets wCoalescedWebs
     return $ (igAdjLists g M.! i) S.\\ (select `S.union` coalesced)

-- | Takes a web id and gives the current list of "move-related" nodes. "NodeMoves"
webMoves :: WebID -> AM (S.Set MovePtr)
webMoves i = 
    do wmoves <- gets $ getWebMoves' i
       actives <- gets wActiveMoves
       worklist <- gets wWorklistMoves
       return $ wmoves `S.intersection` (actives `S.union` worklist)

-- | Takes a web id and tells whether it's "move-related"
moveRelated :: WebID -> AM Bool
moveRelated i = (not . S.null) `fmap` webMoves i

makeWorklists :: InterfGraph -> M.Map Label Int -> RWorklists
makeWorklists g loops = wl'
    where wl = iter (igWebIDs g) (initWorklists g initMoves moves idealRegs loops)
          wl' = wl { wSpillCosts = M.fromList $ map (\i -> (i, spillCost wl i)) $ igWebIDs g }
          
          iter [] wlists = wlists
          iter (i:is) wlists
              | webPrecolored web
                  = iter is (wlists
                             { wColoredWebs = M.insert i (x86Reg $ webReg web)
                                              (wColoredWebs wlists)
                             , wPrecoloredWebs = S.insert i (wPrecoloredWebs wlists)
                             , wDegrees = M.insert i maxBound (wDegrees wlists) })
              | webDegree i g >= numUsableRegisters
                  = iter is (wlists { wSpillWorklist = i:(wSpillWorklist wlists) })
              | evalState (moveRelated i) wlists
                  = iter is (wlists { wFreezeWorklist = i:(wFreezeWorklist wlists) })
              | otherwise
                  = iter is (wlists { wSimplifyWorklist = i:(wSimplifyWorklist wlists) })
              where web = igGetWeb i g
          initMoves = igRRMoves g
          moves = M.fromList $ map (\l -> (l, websWithLabel l)) $ S.toList $ igRRMoves g
          websWithLabel l = M.keys $ M.filter cond $ igIDToWeb g
              where cond w = l `S.member` (webDefs w) || l `S.member` (webUses w)
          
          idealRegs :: M.Map WebID [X86Reg]
          idealRegs = M.fromList $ do w <- igWebIDs g
                                      let web = igGetWeb w g
                                          wmoves = S.toList $ webMoveNodes web
                                          nwebs = concatMap (moves M.!) wmoves
                                          mr web (MReg r) = if webPrecolored web then [r] else []
                                          mr web _ = []
                                          nregs = do wn <- nwebs
                                                     let webn = igGetWeb wn g
                                                     mr webn (webReg webn)
                                      return (w, nregs)
                                       

          -- | Sets up everything but the web worklists.
          initWorklists :: InterfGraph -> S.Set NodePtr -> M.Map NodePtr [WebID] -> M.Map WebID [X86Reg] -> M.Map Label Int
              -> RWorklists
          initWorklists g wm moves idealRegs loops
              = RWorklists
                { wInterfGraph = g
                , wSpillWorklist = []
                , wFreezeWorklist = []
                , wSimplifyWorklist = []
                , wSpilledWebs = []
                , wCoalescedWebs = S.empty
                , wColoredWebs = M.empty
                , wPrecoloredWebs = S.empty
                , wSelectStack = []
                , wCoalescedAlias = M.empty
                , wHaveSpilled = False
                , wPreSpillCoalesced = S.empty
                , wPreSpillAlias = M.empty
                , wPreSpillCoalescedMoves = S.empty
                , wDegrees = M.fromList $ map (\i -> (i, webDegree i g)) (igWebIDs g)
                , wSpillCosts = M.empty
                , wWorklistMoves = wm
                , wCoalescedMoves = []
                , wConstrainedMoves = []
                , wFrozenMoves = []
                , wActiveMoves = S.empty
                , wMoves = moves
                , wIdealRegs = idealRegs
                , wLoops = loops
                }

-- | "main"
doRegAlloc :: SpillLocSupply -> Label -> Graph Asm C C -> Graph Asm C C
doRegAlloc spillLocs mlabel graph
    = let pg = toPGraph graph
          dus = collectDU [mlabel] pg
          webs = collectWebs (dus M.! mlabel)
          interfgraph = makeInterfGraph [mlabel] pg webs
          loops = L.loopNestInformation graph [mlabel]
          initState = makeWorklists interfgraph loops
          spilledNodes = evalState (return pg) initState
          -- | runs simplify/coalesce/freeze/selectspill until work
          -- lists are empty
          mainLoop = do wl <- get
                        let mtodo = msum
                                    [ do guard $ not (null $ wSimplifyWorklist wl)
                                         return $ trace' "simplify" simplify
                                    , do guard $ not (S.null $ wWorklistMoves wl)
                                         return $ trace' "coalesce" coalesce
                                    , do guard $ not (null $ wFreezeWorklist wl)
                                         return $ trace' "freeze" freeze
                                    , do guard $ not (null $ wSpillWorklist wl)
                                         return $ trace' "selectSpill" selectSpill
                                    ]
                        case mtodo of
                          Just action -> do action
                                            wl <- get
                                            trace' ("***\n"++displayWL' wl++"***\n") mainLoop
                          Nothing -> return ()
          main = do mainLoop
                    trace' "assignColors" assignColors
                    spilledWebs <- wSpilledWebs `fmap` get
                    wl <- get
                    if trace' ("endState:\n" ++ displayWL wl) $ not $ null spilledWebs
                       then let (spillLocs', graph') = insertSpills spillLocs pg wl
                            in trace' ("spilledCode:\n" ++ unlines (graphToAsm False graph' mlabel)) $ return $ doRegAlloc spillLocs' mlabel graph'
                       else let graph' = rewriteGraph pg wl
                            in trace' ("endCode:\n" ++ unlines (graphToAsm False graph' mlabel)++"\n****\n****\n") $ return graph'
      in evalState main (trace' ("initCode:\n" ++ unlines (graphToAsm False graph mlabel) ++ "\ninitState:\n" ++ displayWL initState) initState)

insertSpills :: SpillLocSupply -> Graph (PNode Asm) C C -> RWorklists 
             -> (SpillLocSupply, Graph Asm C C)
insertSpills spillLocs pg wl = (spillLocs', graph')
    where GMany _ body _ = pg
          graph' = foldl (|*><*|) emptyClosedGraph bodies
          bodies = map f (mapElems body)
          f :: Block (PNode Asm) C C -> Graph Asm C C
          f block = fe e
                    <*> catGraphs (map fm inner)
                    <*> fx x
              where (me, inner, mx) = blockToNodeList block
                    e :: (PNode Asm) C O
                    x :: (PNode Asm) O C
                    e = case me of
                          JustC e' -> e'
                    x = case mx of
                          JustC x' -> x'
          
          fe :: PNode Asm C O -> Graph Asm C O
          fe (PNode l n) = mkFirst n' <*> mkMiddles (map genSpill defined')
              where n' = rewriteCoal l n
                    (used, defined) = getAliveDead n'
                    defined' = filter (\d -> (l, d) `M.member` toSpill) defined
                    genSpill reg = Spill noPosition reg (toSpill M.! (l, reg))
          
          fm :: PNode Asm O O -> Graph Asm O O
          fm (PNode l n) = if l `S.member` wPreSpillCoalescedMoves wl
                           then emptyGraph
                           else mkMiddles $ map genReload used' ++ [n'] ++ map genSpill defined'
              where n' = rewriteCoal l n
                    (used, defined) = getAliveDead n'
                    used' = filter (\u -> (l, u) `M.member` toReload) used
                    defined' = filter (\d -> (l, d) `M.member` toSpill) defined
                    genReload reg = Reload noPosition (toReload M.! (l, reg)) reg
                    genSpill reg = Spill noPosition reg (toSpill M.! (l, reg))
                    
          fx :: PNode Asm O C -> Graph Asm O C
          fx (PNode l n) = mkMiddles (map genReload used') <*> mkLast n'
              where n' = rewriteCoal l n
                    (used, defined) = getAliveDead n'
                    used' = filter (\u -> (l, u) `M.member` toReload) used
                    genReload reg = Reload noPosition (toReload M.! (l, reg)) reg
          
          rewriteCoal :: forall e x. NodePtr -> Asm e x -> Asm e x
          rewriteCoal l n = fromMaybe n $ mapAsm (ms l) (md l) n
          ms l r = Just $ fromMaybe r $ M.lookup (l, r) usesMap
          md l r = Just $ fromMaybe r $ M.lookup (l, r) defsMap
          
          idToWeb :: [(WebID, Web)]
          idToWeb = M.toList $ igIDToWeb (wInterfGraph wl)

          newWebReg :: WebID -> Reg
          newWebReg i = let i' = getPreAlias' i wl
                            web = igIDToWeb (wInterfGraph wl) M.! i'
                        in case webPrecolored web of
                             True -> webReg web
                             False -> SReg $ "web_" ++ show i'
          
          usesMap, defsMap :: M.Map (NodePtr, Reg) Reg
          usesMap = M.fromList $ do (i, w) <- idToWeb
                                    u <- S.toList $ webUses w
                                    return ((u, webReg w), newWebReg i)
          defsMap = M.fromList $ do (i, w) <- idToWeb
                                    u <- S.toList $ webDefs w
                                    return ((u, webReg w), newWebReg i)
          
          spillLocs' = drop (length $ spilled') spillLocs
          
          slmap :: M.Map WebID SpillLoc
          slmap = M.fromList $ zip spilled' spillLocs
          
          spilled' :: [WebID]
          spilled' = map (\i -> getPreAlias' i wl) (wSpilledWebs wl)
          
          spilledWebs :: [(WebID, Web, SpillLoc)]
          spilledWebs = do (i, w) <- idToWeb
                           let i' = getPreAlias' i wl
                           guard $ i' `elem` spilled'
                           return (i', w, slmap M.! i')
          
          toReload, toSpill :: M.Map (NodePtr, Reg) SpillLoc
          toReload = M.fromList $ do (i', w, sl) <- spilledWebs
                                     u <- S.toList $ webUses w
                                     return $ ((u, newWebReg i'), sl)
          toSpill = M.fromList $ do (i', w, sl) <- spilledWebs
                                    d <- S.toList $ webDefs w
                                    return $ ((d, newWebReg i'), sl)

rewriteGraph :: Graph (PNode Asm) C C -> RWorklists -> Graph Asm C C
rewriteGraph pg wl = graph'
    where GMany _ body _ = pg
          graph' = foldl (|*><*|) emptyClosedGraph bodies
          bodies = map f (mapElems body)
          f :: Block (PNode Asm) C C -> Graph Asm C C
          f block = fe e
                    <*> catGraphs (map fm inner)
                    <*> fx x
              where (me, inner, mx) = blockToNodeList block
                    e :: (PNode Asm) C O
                    x :: (PNode Asm) O C
                    e = case me of
                          JustC e' -> e'
                    x = case mx of
                          JustC x' -> x'
          
          fe :: PNode Asm C O -> Graph Asm C O
          fe (PNode l n) = mkFirst n
          
          fm :: PNode Asm O O -> Graph Asm O O
          fm (PNode l n) = case fromMaybe n $ mapAsm fs fd n of
                             MovIRMtoR _ (IRM_R rs) rd
                                 | rs == rd -> emptyGraph
                             n -> mkMiddle n
              where fs r = Just $ fromMaybe r $ M.lookup (l, r) usesColorMap
                    fd r = Just $ fromMaybe r $ M.lookup (l, r) defsColorMap
          
          fx :: PNode Asm O C -> Graph Asm O C
          fx (PNode l n) = mkLast n
          
          idToWeb = M.toList $ igIDToWeb (wInterfGraph wl)
          usesColorMap = M.fromList $ do (i, w) <- idToWeb
                                         u <- S.toList $ webUses w
                                         case M.lookup i (wColoredWebs wl) of
                                           Just r -> return ((u, webReg w), MReg r)
                                           Nothing -> mzero
          defsColorMap = M.fromList $ do (i, w) <- idToWeb
                                         d <- S.toList $ webDefs w
                                         case M.lookup i (wColoredWebs wl) of
                                           Just r -> return ((d, webReg w), MReg r)
                                           Nothing -> mzero


-- | "Simplify"
simplify :: AM ()
simplify = do u <- selectSimplify
              modify $ \wl -> wl { wSimplifyWorklist = delete u $ wSimplifyWorklist wl }
              web <- gets $ wGetWeb u
              trace' ("select " ++ show u) $ pushSelect u
              (S.toList `fmap` adjacentWebs u) >>= mapM_ decrementDegree

-- | Chooses the web to simplify
selectSimplify :: AM WebID
selectSimplify =
  do wl@(RWorklists { wSimplifyWorklist = choices }) <- get
     x <- choose choices
     return x
    where
      choose (x:xs) = return x
      choose _ = error "nothing to select for simplify! :-("

 -- | Decrements the degree of the web in the
 -- worklist. "DecrementDegree"
decrementDegree :: WebID -> AM ()
decrementDegree i =
    do wl <- get
       let d = wDegrees wl M.! i
       put $ wl { wDegrees = M.adjust (subtract 1) i (wDegrees wl) }
       when (d == numUsableRegisters) $ do
         enableMoves i
         adj <- S.toList `fmap` adjacentWebs i
         mapM_ enableMoves adj
         modify $ \wl -> wl { wSpillWorklist = delete i (wSpillWorklist wl) }
         mr <- moveRelated i
         modify $ \wl -> if mr
                         then wl { wFreezeWorklist = i:(delete i $ wFreezeWorklist wl) }
                         else wl { wSimplifyWorklist = i:(delete i $ wSimplifyWorklist wl) }

-- | "EnableMoves"
enableMoves :: WebID -> AM ()
enableMoves i = do moves <- S.toList `fmap` webMoves i
                   forM_ moves $ \m -> do
                     activeMoves <- gets wActiveMoves
                     when (m `S.member` activeMoves) $
                          do modify $ \wl -> wl { wActiveMoves = S.delete m activeMoves
                                                , wWorklistMoves = S.insert m (wWorklistMoves wl) }

-- | "Coalesce"
coalesce :: AM ()
coalesce = do m <- selectMove
              [x, y] <- gets $ \wl -> fixList $ wMoves wl M.! m
              [x, y] <- mapM getAlias [x, y]
              idToWeb <- gets $ igIDToWeb . wInterfGraph
              let yPC = webPrecolored $ idToWeb M.! y
              let (u, v) = if yPC then (y, x) else (x, y)
              -- Invariant: if either u,v is fixed, then u is fixed.
              wl <- get
              let uweb = idToWeb M.! u
                  vweb = idToWeb M.! v
                  adjuv = isAdj u v wl
              adjacentu <- adjacentWebs u
              adjacentv <- adjacentWebs v
              okadjv <- and `fmap` mapM (\t -> ok t u) (S.toList adjacentv)
              conserv <- conservative $ adjacentu `S.union` adjacentv
              cond $
                [
                 ( u == v
                 , do modify $ \wl -> wl { wCoalescedMoves = m:(wCoalescedMoves wl)
                                         , wPreSpillCoalescedMoves = (if wHaveSpilled wl
                                                                      then id
                                                                      else S.insert m) (wPreSpillCoalescedMoves wl) }
                      addWorklist u
                 )
                ,( webPrecolored vweb || adjuv
                 , do modify $ \wl -> wl { wConstrainedMoves = m:(wConstrainedMoves wl) }
                      addWorklist u
                      addWorklist v
                 )
                ,( (webPrecolored uweb && (okadjv)) -- || isShortWeb vweb))
                    || (not (webPrecolored uweb) && conserv)
                 , do modify $ \wl -> wl { wCoalescedMoves = m:(wCoalescedMoves wl)
                                         , wPreSpillCoalescedMoves = (if wHaveSpilled wl
                                                                      then id
                                                                      else S.insert m) (wPreSpillCoalescedMoves wl) }
                      combine u v
                      addWorklist u
                 )
                ,( True
                 , do modify $ \wl -> wl { wActiveMoves = S.insert m $ wActiveMoves wl }
                 )
                ]
    where cond :: Monad m => [(Bool, m ())] -> m ()
          cond opts = fromMaybe (return ()) $ msum $ map (\(b,m) -> guard b >> return m) opts
          
          fixList [a] = [a,a]
          fixList xs = xs
          
          -- r is the web of a fixed register, and t is a neighbor of a neighbor of r
          ok t r = do wl <- get
                      let degt = wDegrees wl M.! t
                          tweb = igIDToWeb (wInterfGraph wl) M.! t
                          adjtr = S.member r (igAdjLists (wInterfGraph wl) M.! t)
                      return $ webPrecolored tweb || degt < numUsableRegisters || adjtr
                      -- "webPrecolored tweb" means that coalescing won't make r and t interfere
                      -- "degt < numUsableRegisters" means that t's a low-degree node
                      -- "adjtr" means that t and r already interfere
          
          conservative nodes = do wl <- get
                                  return $ length (sigDegs wl) < numUsableRegisters
              where sigDegs wl
                        = [n | n <- S.toList nodes, wDegrees wl M.! n >= numUsableRegisters]
          
          -- | Removes a web from the freeze worklist and puts it into
          -- the simplify worklist if it is no longer move-related and
          -- is of insignificant degree
          addWorklist :: WebID -> AM ()
          addWorklist u =
              do wl <- get
                 let uweb = igIDToWeb (wInterfGraph wl) M.! u
                     deg = wDegrees wl M.! u
                     precolored = webPrecolored uweb
                 moverelated <- moveRelated u
                 when (not precolored && not moverelated && deg < numUsableRegisters) $ do
                   modify $ \wl -> wl { wFreezeWorklist = delete u $ wFreezeWorklist wl
                                      , wSimplifyWorklist = u:(wSimplifyWorklist wl) }

selectMove :: AM NodePtr
selectMove = do wl@(RWorklists { wWorklistMoves = choices }) <- get
                x <- choose $ S.toList choices
                put $ wl { wWorklistMoves = S.delete x choices }
                return x
    where choose (x:xs) =
              do return x


-- | "Combine"
combine :: WebID -> WebID -> AM ()
combine u v =
    do modify $ trace' ("combine " ++ show u ++ " " ++ show v) $ \wl ->
           case v `elem` wFreezeWorklist wl of
             True -> wl { wFreezeWorklist = delete v $ wFreezeWorklist wl }
             False -> wl { wSpillWorklist = delete v $ wSpillWorklist wl }
       modify $ \wl -> wl { wCoalescedWebs = S.insert v $ wCoalescedWebs wl
                          , wCoalescedAlias = M.insert v u $ wCoalescedAlias wl 
                          , wPreSpillCoalesced = (if wHaveSpilled wl
                                                  then id
                                                  else S.insert v) (wPreSpillCoalesced wl)
                          , wPreSpillAlias = (if wHaveSpilled wl
                                              then id
                                              else M.insert v u) (wPreSpillAlias wl)
                          }
--       webmovesu <- gets $ getWebMoves' u
--       webmovesv <- gets $ getWebMoves' v
--       modify $ updateWebMoves' (webmovesu `S.union` webmovesv) u
       modify $ \wl -> combineWebs u v wl
       modify $ \wl -> wl { wIdealRegs = M.insert u (nub $
                                                     (wIdealRegs wl M.! u)
                                                     ++ (wIdealRegs wl M.! v)) 
                                         (wIdealRegs wl) }
       adjv' <- S.toList `fmap` adjacentWebs v
       forM_ adjv' $ \t -> do
         trace' ("  addToAdjList " ++ show t ++ " " ++ show u) $ addToAdjList t u
         decrementDegree t
       wl <- get
       let d = wDegrees wl M.! u
       when (d >= numUsableRegisters
             && u `elem` wFreezeWorklist wl) $ do
         modify $ \wl -> wl { wFreezeWorklist = delete u $ wFreezeWorklist wl
                            , wSpillWorklist = u:(wSpillWorklist wl) }

-- | "GetAlias"
getAlias :: WebID -> AM WebID
getAlias i = gets $ getAlias' i

getAlias' :: WebID -> RWorklists -> WebID
getAlias' i wl = case i `S.member` wCoalescedWebs wl of
                   True -> getAlias' (wCoalescedAlias wl M.! i) wl
                   False -> i

getPreAlias' :: WebID -> RWorklists -> WebID
getPreAlias' i wl = case i `S.member` wPreSpillCoalesced wl of
                      True -> getPreAlias' (wPreSpillAlias wl M.! i) wl
                      False -> i

-- | "Freeze"
freeze :: AM ()
freeze = do u <- selectFreeze
            modify $ \wl -> wl { wFreezeWorklist = delete u $ wFreezeWorklist wl
                               , wSimplifyWorklist = u:(wSimplifyWorklist wl) }
            freezeMoves (trace' ("freeze " ++ show u) u)
    where selectFreeze = do (u:_) <- gets wFreezeWorklist
                            return u

-- | "FreezeMoves"
freezeMoves :: Int -> AM ()
freezeMoves u = do u <- getAlias u
                   wmoves <- trace' ("freezing: " ++ show u) $ webMoves u
                   wl <- get
                   let wmoves' = map (\l -> (l, map (flip getAlias' wl) $ wMoves wl M.! l)) $ S.toList wmoves
                   -- wmoves' is [(moveptr, [webids])]
                   forM_ (filter (elem u . snd) wmoves') $ \(m,uv) -> do
                     let [v] = delete u $ fixList uv
                     modify $ \wl ->
                       case trace' ("  freeze: " ++ show u ++ " " ++ show v) $ m `S.member` wActiveMoves wl of
                         True -> wl { wActiveMoves = S.delete m $ wActiveMoves wl }
                         False -> wl { wWorklistMoves = S.delete m $ wWorklistMoves wl }
                     modify $ \wl -> wl { wFrozenMoves = m:(delete m $ wFrozenMoves wl) }
                     wmv <- webMoves v
                     degv <- gets $ \wl -> wDegrees wl M.! v
                     when (S.null wmv && degv < numUsableRegisters) $ do
                       modify $ \wl -> wl { wFreezeWorklist = delete v $ wFreezeWorklist wl
                                          , wSimplifyWorklist = v:(wSimplifyWorklist wl) }
    where fixList [a] = [a, a]
          fixList xs = xs

spillCost :: RWorklists -> WebID -> Int
spillCost wl i = let web = igGetWeb i $ wInterfGraph wl
                     deg = wDegrees wl M.! i
                     loopDepth l = M.findWithDefault 0 (nodeLabel l) (wLoops wl)
                     loadCost = sum $ map (\l -> 10 ^ (loopDepth l)) (S.toList (webUses web) ++ S.toList (webDefs web))
                     size = S.size (webExtent web) --sum (map len dus)
                     score = 1000 * loadCost `div` (max 1 deg) --S.size (webExtent web))
                 in if isShortWeb web then maxBound else score

-- | "SelectSpill"
selectSpill :: AM ()
selectSpill = do wl <- get
                 m <- chooseSpill $ wSpillCosts wl
                 modify $ \wl -> wl { wSpillWorklist = delete m $ wSpillWorklist wl
                                    , wSimplifyWorklist = m:(wSimplifyWorklist wl)
                                    , wHaveSpilled = True }
                 trace' ("spilling: " ++ show m) $ freezeMoves m
    where chooseSpill :: M.Map WebID Int -> AM WebID
          chooseSpill costs =
              do wl <- get
                 let spillList = wSpillWorklist wl
                     costs' = map (\i -> (i, costs M.! i)) spillList
                     costs'' = map (\i -> (i, webReg $ igGetWeb i (wInterfGraph wl), costs M.! i)) spillList
                 return $ trace' ("costs: " ++ show costs'') $ fst $ minimumBy (compare `on` snd) costs'

-- | "AssignColors"
assignColors :: AM ()
assignColors = do emptyStack
                  wl <- get
                  forM_ (S.toList $ wCoalescedWebs wl) $ \n -> do
                    alias <- getAlias n
                    modify $ \wl -> wl { wColoredWebs = M.insert n (wColoredWebs wl M.! alias) 
                                                        (wColoredWebs wl) }
    where emptyStack :: AM ()
          emptyStack
              = do wl <- get
                   when (not $ null $ wSelectStack wl) $ do
                     n <- popSelect
                     web <- gets $ igGetWeb n . wInterfGraph
                     wl <- get
                     okColors <- determineColors n 
                     case okColors of
                       [] -> modify $ \wl -> wl { wSpilledWebs = n:(wSpilledWebs wl) }
                       (c:_) -> modify $ \wl ->
                                   wl { wColoredWebs = M.insert n c (wColoredWebs wl) }
                     emptyStack
          
          determineColors :: WebID -> AM [X86Reg]
          determineColors n = do wl <- get
                                 let adj = S.toList $ igAdjLists (wInterfGraph wl) M.! n
                                 adj' <- mapM getAlias adj
                                 allcolored <- gets wColoredWebs
                                 let colored = filter (`M.member` allcolored) adj'
                                     usedColors = map (allcolored M.!) colored
                                     ok = usableRegisters \\ usedColors
                                     nregs = wIdealRegs wl M.! n
                                     nnregs = concatMap (wIdealRegs wl M.!) adj'
                                     (ok1, ok2) = partition (`notElem` nnregs) ok
                                     (ok1', ok2') = partition (`elem` nregs) (ok1 ++ ok2)
                                 return $ ok1' ++ ok2'

outputWebGraph :: InterfGraph -> String
outputWebGraph ig
    = "graph {\n"
      ++ "_webs_ [shape=record,label=\"{" ++ intercalate "|" (map showWeb webs) ++ "}\"];\n"
      ++ "_moves_ [shape=record,label=\"" ++ show (igRRMoves ig) ++ "\"];\n"
      ++ labels
      ++ edges
      ++ "}"
    where mkEdges i web = do
            j <- S.toList $ g M.! i
            guard $ i < j
            show i ++ " -- " ++ show j ++ ";\n"
          edges = do (i, web) <- webs
                     mkEdges i web
          labels = do (i, web) <- webs
                      show i ++ " [label=\"" ++ show i ++ ": " ++ show (webReg web) ++ "\"];\n"
          showWeb (i, web) = "{" ++ intercalate "|" [show i, wr, wmr, wf, wd, we, wu] ++ "}"
              where wr = show $ webReg web
                    wmr = "moves: " ++ show (S.toList $ webMoveNodes web)
                    wf = if webPrecolored web then "precolored" else "free"
                    wd = show $ webDefs web
                    we = show $ webExtent web
                    wu = show $ webUses web
          webs = M.toList $ igIDToWeb ig
          g = igAdjLists ig



