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
import Util.NodeLocate
import qualified LoopAnalysis as L
import RegAlloc.InterfGraph

dotrace = False

trace' a b = if dotrace then trace a b else b 

-- | Main entry point to allocating registers for the IR
regAlloc :: LowIRRepr -> I.GM LowIRRepr
regAlloc lir
    = do LowIRRepr fields strs meths graph <- evalStupidFuelMonad (performDeadAsmPass lir) 2222222
         let GMany _ body _ = graph
             mlabels = map I.methodEntry meths
         massgraph <- evalStupidFuelMonad (massageGraph mlabels graph) 22222222
         --graph' <- error $ I.graphToGraphViz show massgraph
         let graph' = foldl (flip id) massgraph (map (doRegAlloc freeSpillLocs) mlabels)
         graph'' <- evalStupidFuelMonad (collectSpill mlabels graph') 22222222
         return $ LowIRRepr fields strs meths graph''



-- | Collects and rewrites the spills in the graph to moves.
collectSpill :: [Label] -> Graph A.Asm C C -> RM (Graph A.Asm C C)
collectSpill mlabels graph
    = do (_, f, _) <- analyzeAndRewriteBwd
                      collectSpillPass
                      (JustC mlabels)
                      graph
                      mapEmpty
         (g, _, _) <- analyzeAndRewriteFwd
                      (rewriteSpillPass f)
                      (JustC mlabels)
                      graph
                      f
         return g


-- | Gets the list of spills for each entry point. TODO: make it also
-- find live ranges for spills so we can reuse stack space.
collectSpillPass :: (CheckpointMonad m, FuelMonad m)
                    => BwdPass m A.Asm (S.Set SpillLoc)
collectSpillPass = BwdPass
                   { bp_lattice = getSpillLattice
                   , bp_transfer = getSpillTransfer
                   , bp_rewrite = noBwdRewrite }
    where
      getSpillLattice :: DataflowLattice (S.Set SpillLoc)
      getSpillLattice = DataflowLattice
                        { fact_name = "spill lattice"
                        , fact_bot = S.empty
                        , fact_join = add
                        }
          where add _ (OldFact old) (NewFact new) = (ch, j)
                    where j = S.union new old
                          ch = changeIf $ S.size j > S.size old

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

-- | Rewrites the spills to moves.
rewriteSpillPass :: (CheckpointMonad m, FuelMonad m) =>
                    FactBase (S.Set SpillLoc) -> FwdPass m Asm (S.Set SpillLoc)
rewriteSpillPass fb = FwdPass 
                      { fp_lattice = noLattice
                      , fp_transfer = sTransfer
                      , fp_rewrite = rewriteSpill }
    where noLattice :: DataflowLattice (S.Set SpillLoc)
          noLattice = DataflowLattice
                      { fact_name = "simple replicate"
                      , fact_bot = S.empty
                      , fact_join = add }
              where add _ (OldFact old) (NewFact new) = (ch, j)
                        where j = S.union new old
                              ch = changeIf $ S.size j > S.size old
          sTransfer :: FwdTransfer Asm (S.Set SpillLoc)
          sTransfer = mkFTransfer3 g g' g''
              where 
                g :: Asm C O -> S.Set SpillLoc -> S.Set SpillLoc
                g (Enter p l _ _) _ = fromMaybe S.empty (lookupFact l fb)
                g e f = f
                g' e f = f
                g'' e f = mkFactBase noLattice $ zip (successors e) (repeat f)

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

-- | Updates webMoveNodes to the given value for the web id
updateWebMoves' :: S.Set MovePtr -> WebID -> RWorklists -> RWorklists
updateWebMoves' s i wl
    = wl { wInterfGraph = g { igIDToWeb = M.insert i web' $ igIDToWeb g }}
    where g = wInterfGraph wl
          web = igIDToWeb g M.! i
          web' = web { webMoveNodes = s }
          
combineWebs :: WebID -> WebID -> RWorklists -> RWorklists
combineWebs i1 i2 wl
  = wl { wInterfGraph = g { igIDToWeb = M.insert i1 web' $ igIDToWeb g }}
    where g = wInterfGraph wl
          web1 = igIDToWeb g M.! i1
          web2 = igIDToWeb g M.! i2
          web' = wUnion web1 web2

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

-- | Takes a web id and gives the current list of "move-related" webs. "NodeMoves"
webMoves :: Int -> AM (S.Set NodePtr)
webMoves i = 
    do wmoves <- gets $ getWebMoves' i
       actives <- gets wActiveMoves
       worklist <- gets wWorklistMoves
       return $ wmoves `S.intersection` (actives `S.union` worklist)

-- | Takes a web id and tells whether it's "move-related"
moveRelated :: WebID -> AM Bool
moveRelated i = (not . S.null) `fmap` webMoves i

makeWorklists :: InterfGraph -> M.Map Label Int -> RWorklists
makeWorklists g loops = iter (igWebIDs g) (initWorklists g initMoves moves idealRegs loops)
    where iter [] wlists = wlists
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
          initMoves = S.map (\(l,_,_) -> l) $ igRRMoves g
          moves = M.fromList $ map (\(l,_,_) -> (l, websWithLabel l)) $ S.toList $ igRRMoves g
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
          rrfacts = getRegRegMoves [mlabel] pg
          interfgraph = makeInterfGraph webs (rrfacts M.! mlabel)
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
                                            mainLoop
                          Nothing -> return ()
          main = do trace ("asm:\n" ++ I.graphToGraphViz show graph ++ "\n\n") mainLoop
                    trace' "assignColors" assignColors
                    spilledWebs <- wSpilledWebs `fmap` get
                    wl <- get
                    if not $ null spilledWebs
                       then let (spillLocs', graph') = insertSpills spillLocs pg wl
                            in return $ doRegAlloc spillLocs' mlabel graph'
                       else return $ trace' ("done: " ++ show wl) $ rewriteGraph pg wl
      in evalState main (trace' ("initState: " ++ show initState) initState)

insertSpills :: SpillLocSupply -> Graph (PNode Asm) C C -> RWorklists 
             -> (SpillLocSupply, Graph Asm C C)
insertSpills spillLocs pg wl = trace' ("insertSpills: " ++ show toSpill ++ show toReload) (spillLocs', graph')
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
                    
          rewriteCoal l n = mapAsm (ms l) (md l) n
          ms l r = fromMaybe r $ M.lookup (l, r) usesMap
          md l r = fromMaybe r $ M.lookup (l, r) defsMap
          
          idToWeb = M.toList $ igIDToWeb (wInterfGraph wl)
          
          usesMap, defsMap :: M.Map (NodePtr, Reg) Reg
          usesMap = M.fromList $ do (i, w) <- idToWeb
                                    let i' = getPreAlias' i wl
                                        r' = webReg $ (igIDToWeb (wInterfGraph wl)) M.! i'
                                    u <- S.toList $ webUses w
                                    return ((u, webReg w), r')
          defsMap = M.fromList $ do (i, w) <- idToWeb
                                    let i' = getPreAlias' i wl
                                        r' = webReg $ (igIDToWeb (wInterfGraph wl)) M.! i'
                                    u <- S.toList $ webDefs w
                                    return ((u, webReg w), r')
          
          spillLocs' = drop (length $ spilled') spillLocs
          
          slmap :: M.Map WebID SpillLoc
          slmap = M.fromList $ zip spilled' spillLocs
          
          spilled' :: [WebID]
          spilled' = map (\i -> getPreAlias' i wl) (wSpilledWebs wl)
          
          spilledWebs :: [(Web, SpillLoc)]
          spilledWebs = do (i, w) <- idToWeb
                           let i' = getPreAlias' i wl
                           guard $ i' `elem` spilled'
                           return (w, slmap M.! i')
          
          toReload, toSpill :: M.Map (NodePtr, Reg) SpillLoc
          toReload = M.fromList $ do (w, sl) <- spilledWebs
                                     u <- S.toList $ webUses w
                                     return $ ((u, webReg w), sl)
          toSpill = M.fromList $ do (w, sl) <- spilledWebs
                                    d <- S.toList $ webDefs w
                                    return $ ((d, webReg w), sl)

rewriteGraph :: Graph (PNode Asm) C C -> RWorklists -> Graph Asm C C
rewriteGraph pg wl = trace' ("rewriteGraph: " ++ show usesColorMap ++ show defsColorMap) graph'
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
          fm (PNode l n) = case mapAsm fs fd n of
                             MovIRMtoR _ (IRM_R rs) rd
                                 | rs == rd -> emptyGraph
                             n -> mkMiddle n
              where fs r = fromMaybe r $ M.lookup (l, r) usesColorMap
                    fd r = fromMaybe r $ M.lookup (l, r) defsColorMap
          
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
              trace' ("pushSelect " ++ show u ++ " = " ++ show (webReg web)) $ pushSelect u
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
                         then wl { wFreezeWorklist = i:(wFreezeWorklist wl) }
                         else wl { wSimplifyWorklist = i:(wSimplifyWorklist wl) }

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
    do modify $ \wl ->
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
         addToAdjList t u
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
            freezeMoves(u)
    where selectFreeze = do (u:_) <- gets wFreezeWorklist
                            return u

-- | "FreezeMoves"
freezeMoves :: Int -> AM ()
freezeMoves u = do wmoves <- trace ("freezing: " ++ show u) $ webMoves u
                   wl <- get
                   let wmoves' = map (\l -> (l, wMoves wl M.! l)) $ S.toList wmoves
                   forM_ (filter (elem u . snd) wmoves') $ \(m,uv) -> do
                     let [v] = delete u uv
                     modify $ \wl ->
                       case trace ("  freeze: " ++ show u ++ " " ++ show v) $ m `S.member` wActiveMoves wl of
                         True -> wl { wActiveMoves = S.delete m $ wActiveMoves wl }
                         False -> wl { wWorklistMoves = S.delete m $ wWorklistMoves wl }
                     modify $ \wl -> wl { wFrozenMoves = m:(wFrozenMoves wl) }
                     wmv <- webMoves v
                     degv <- gets $ \wl -> wDegrees wl M.! v
                     when (S.null wmv && degv < numUsableRegisters) $ do
                       modify $ \wl -> wl { wFreezeWorklist = delete v $ wFreezeWorklist wl
                                          , wSimplifyWorklist = v:(wSimplifyWorklist wl) }


-- | "SelectSpill"
selectSpill :: AM ()
selectSpill = do wl <- get
                 m <- chooseSpill $ makeCosts wl
                 modify $ \wl -> wl { wSpillWorklist = delete m $ wSpillWorklist wl
                                    , wSimplifyWorklist = m:(wSimplifyWorklist wl)
                                    , wHaveSpilled = True }
                 trace ("spilling: " ++ show m) $ freezeMoves m
    where chooseSpill :: M.Map WebID Int -> AM WebID
          chooseSpill costs =
              do wl <- get
                 let spillList = wSpillWorklist wl
                     costs' = map (\i -> (i, costs M.! i)) spillList
                     costs'' = map (\i -> (i, webReg $ igGetWeb i (wInterfGraph wl), costs M.! i)) spillList
                 return $ trace ("costs: " ++ show costs'') $ fst $ minimumBy (compare `on` snd) costs'
          makeCosts :: RWorklists -> M.Map WebID Int
          makeCosts wl = M.fromList $ map (\i -> (i, cost wl i)) $ wSpillWorklist wl
          cost :: RWorklists -> WebID -> Int
          cost wl i = let web = igGetWeb i $ wInterfGraph wl
                          deg = wDegrees wl M.! i
                          loopDepth l = M.findWithDefault 0 (nodeLabel l) (wLoops wl)
                          loadCost = sum $ map (\l -> 10 ^ (loopDepth l)) (S.toList (webUses web) ++ S.toList (webDefs web))
                          uses = max 1 (S.size $ webUses web)
                          size = S.size (webExtent web) --sum (map len dus)
--                          score = (deg * size) `div` (uses)
                          score = 1000 * loadCost `div` (1 + S.size (webExtent web))
                      in if isShortWeb web then maxBound else score

-- | "AssignColors"
assignColors :: AM ()
assignColors = do emptyStack
                  wl <- get
                  forM_ (S.toList $ wCoalescedWebs (trace' (outputWebGraph $ wInterfGraph wl) wl)) $ \n -> do
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
                     case trace' (show n ++ " " ++ show (webReg web) ++ " okColors: " ++ show okColors ++ " " ++ show (igAdjLists (wInterfGraph wl) M.! n) ++ " " ++ show (wColoredWebs wl)) okColors of
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



