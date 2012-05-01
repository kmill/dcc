{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

-- | We kind of follow "Iterated Register Coalescing" by Lal George
-- and Andrew Appel.
module RegisterAllocator where 

import qualified Data.Map as M
import Assembly
import qualified Assembly as A
import AliveDead
import CodeGenerate
import qualified IR as I
import Dataflow
import Dataflow.DeadCodeAsm
import qualified Data.Set as S
import Data.List
import Control.Monad.State
import Compiler.Hoopl
import Data.Maybe
import AST (SourcePos, noPosition)
import Debug.Trace

import Data.Function
import Util.NodeLocate

regAlloc :: LowIRRepr -> I.GM LowIRRepr
regAlloc lir
    = do --graph'' <- evalStupidFuelMonad (collectSpill mlabels graph') 22222222
         return $ LowIRRepr fields strs meths graph'
      where LowIRRepr fields strs meths graph = I.runGM $ evalStupidFuelMonad (performDeadAsmPass lir) 2222222
            GMany _ body _ = graph
            graph' = foldl (flip id) graph (map (doRegAlloc freeSpillLocs) mlabels)
            mlabels = map I.methodEntry meths
--            graph' = error $ I.graphToGraphViz show g'
--            graph' = foldl (|*><*|) emptyClosedGraph bodies
--             bodies = map f (mapElems body)
--             f :: Block Asm C C -> Graph Asm C C
--             f block = mkFirst e
--                       <*> catGraphs (map withSpills inner)
--                       <*> mkLast x
--                 where (me, inner, mx) = blockToNodeList block
--                       e :: Asm C O
--                       x :: Asm O C
--                       e = case me of
--                             JustC e' -> e'
--                       x = case mx of
--                             JustC x' -> x'

collectSpill :: [Label] -> Graph A.Asm C C -> RM (Graph A.Asm C C)
collectSpill mlabels graph
--     = do (_, f, _) <- analyzeAndRewriteBwd
--                       collectSpillPass
--                       (JustC mlabels)
--                       graph
--                       mapEmpty
--          (g, _, _) <- analyzeAndRewriteFwd
--                       (rewriteSpillPass f)
--                       (JustC mlabels)
--                       graph
--                       f
        = return graph



-- collectSpillPass :: (CheckpointMonad m, FuelMonad m)
--                     => BwdPass m A.Asm (S.Set String)
-- collectSpillPass = BwdPass
--                    { bp_lattice = getSpillLattice
--                    , bp_transfer = getSpillTransfer
--                    , bp_rewrite = noBwdRewrite }
--     where
--       getSpillLattice :: DataflowLattice (S.Set String)
--       getSpillLattice = DataflowLattice
--                         { fact_name = "spill lattice"
--                         , fact_bot = S.empty
--                         , fact_join = add
--                         }
--           where add _ (OldFact old) (NewFact new) = (ch, j)
--                     where j = S.union new old
--                           ch = changeIf $ S.size j > S.size old

--       getSpillTransfer :: BwdTransfer A.Asm (S.Set String)
--       getSpillTransfer = mkBTransfer3 usedCO usedOO usedOC
--           where
--             usedCO :: A.Asm C O -> (S.Set String) -> (S.Set String)
--             usedCO _ f = f

--             usedOO :: A.Asm O O -> (S.Set String) -> (S.Set String)
--             usedOO (A.Spill _ _ s) f = S.insert s f
--             usedOO (A.Reload _ s _) f = S.insert s f
--             usedOO _ f = f

--             usedOC :: A.Asm O C -> FactBase (S.Set String) -> (S.Set String)
--             usedOC x f = S.unions $ map
--                          ((fromMaybe S.empty) . (flip lookupFact f))
--                          (successors x)

-- rewriteSpillPass :: (CheckpointMonad m, FuelMonad m) =>
--                     FactBase (S.Set String) -> FwdPass m Asm (S.Set String)
-- rewriteSpillPass fb = FwdPass 
--                       { fp_lattice = noLattice
--                       , fp_transfer = sTransfer
--                       , fp_rewrite = rewriteSpill }
--     where noLattice :: DataflowLattice (S.Set String)
--           noLattice = DataflowLattice
--                       { fact_name = "simple replicate"
--                       , fact_bot = S.empty
--                       , fact_join = add }
--               where add _ (OldFact old) (NewFact new) = (ch, j)
--                         where j = S.union new old
--                               ch = changeIf $ S.size j > S.size old
--           sTransfer :: FwdTransfer Asm (S.Set String)
--           sTransfer = mkFTransfer3 g g' g''
--               where 
--                 g :: Asm C O -> S.Set String -> S.Set String
--                 g (Enter p l _ _) _ = fromMaybe S.empty (lookupFact l fb)
--                 g e f = f
--                 g' e f = f
--                 g'' e f = mkFactBase noLattice $ zip (successors e) (repeat f)

--           rewriteSpill :: forall m. FuelMonad m => FwdRewrite m Asm (S.Set String)
--           rewriteSpill = mkFRewrite d
--               where 
--                 d :: Asm e x -> S.Set String -> m (Maybe (Graph Asm e x))
--                 d (A.Spill pos reg s) f
--                     = return $ Just $ mkMiddle $ A.mov pos reg mem
--                       where offset = negate (8 + 8 * (fromJust $ elemIndex s f'))
--                             f' = S.toAscList (S.insert s f)
--                             mem = A.MemAddr (Just $ A.MReg A.RBP)
--                                   (A.Imm32 $ fromIntegral offset)
--                                   Nothing A.SOne
--                 d (A.Reload pos s reg) f
--                     = return $ Just $ mkMiddle $ A.mov pos mem reg
--                       where offset = negate (8 + 8 * (fromJust $ elemIndex s f'))
--                             f' = S.toAscList (S.insert s f)
--                             mem = A.MemAddr (Just $ A.MReg A.RBP)
--                                   (A.Imm32 $ fromIntegral offset)
--                                   Nothing A.SOne
--                 d (A.Enter pos l n x) f = if x' == x
--                                           then return Nothing
--                                           else return $ Just $ mkFirst $
--                                                A.Enter pos l n x'
--                     where x' = fromIntegral $ 8 * (S.size f) + 8
--                 d _ f = return Nothing



freeRegs :: [Reg]
freeRegs = map MReg [R10, R11, R12, R13, R14, R15] -- put this in optimal order!

getSRegs :: [Reg] -> [String]
getSRegs [] = []
getSRegs ((SReg s):xs) = s:(getSRegs xs)
getSRegs (_:xs) = getSRegs xs

-- withSpills :: Asm O O -> Graph Asm O O
-- withSpills expr = reloads <*> expr' <*> spills
--     where
--       (alive, dead) = getAliveDead expr
--       salive = getSRegs alive
--       sdead = getSRegs dead
--       sToRegs = zip (salive ++ sdead) freeRegs
--       f :: Reg -> Reg
--       f (SReg s) = getMReg s
--       f r = r
--       getMReg s = fromJust $ lookup s sToRegs
--       expr' = mkMiddle $ mapRR f expr
--       mkReload s = mkMiddle $ Reload noPosition s (getMReg s)
--       mkSpill s = mkMiddle $ Spill noPosition (getMReg s) s
--       reloads = catGraphs $ map mkReload salive
--       spills = catGraphs $ map mkSpill sdead

---
--- Webs
---
      
data DU = DU { duReg :: Reg
             , duSpilled :: Bool
             , duMoveNodes :: S.Set NodePtr
             , duFixed :: Bool
             , duDef :: NodePtr
             , duExtent :: S.Set NodePtr
             , duUse :: NodePtr }
        | DUv { duReg :: Reg
              , duSpilled :: Bool
              , duFixed :: Bool
              , duDef :: NodePtr } -- ^ Represents a register which is
                                   -- defined but not used.  It should
                                   -- still be given a chance to
                                   -- interfere!
          deriving (Eq, Ord, Show)
data Web = Web { webReg :: Reg
               , webSpilled :: Bool
               , webMoveNodes :: S.Set NodePtr
               , webFixed :: Bool
               , webDUs :: S.Set DU
               , webDefs :: S.Set NodePtr
               , webExtent :: S.Set NodePtr
               , webUses :: S.Set NodePtr }
         deriving (Show, Eq, Ord)

-- | Represents the reg to reg moves
type RRFact = S.Set (NodePtr, Reg, Reg)

data InterfGraph = InterfGraph
    { igIntToWeb :: M.Map Int Web
    , igAdjLists :: M.Map Int (S.Set Int)
    , igRRMoves :: RRFact
    }
                   deriving Show

type InterfGraphs = M.Map Label InterfGraph

addInterfEdge :: Int -> Int -> InterfGraph -> InterfGraph
addInterfEdge u v g = g { igAdjLists = add u v $ add v u $ igAdjLists g }
    where add a b adj = M.adjust (S.insert b) a adj

-- | Checks whether two webs interfere
wInterf :: Web -> Web -> Bool
wInterf (Web r1 _ _ _ dus1 ds1 ex1 us1) (Web r2 _ _ _ dus2 ds2 ex2 us2)
    = if notUsable r1 || notUsable r2
      then False
      else (S.union ds1 ex1 `ints` S.union ds2 ex2)
               || (S.union ex1 us1 `ints` S.union ex2 us2)
      where ints s1 s2 = not $ S.null $ s1 `S.intersection` s2
            notUsable (MReg r) = r `notElem` usableRegisters
            notUsable (SReg _) = False


-- | Gets the degree of a web in the interference graph.
webDegree :: Int -> InterfGraph -> Int
webDegree i g = S.size $ igAdjLists g M.! i

-- | Gets the list of web ids from an interference graph.
igWebIDs :: InterfGraph -> [Int]
igWebIDs g = M.keys $ igIntToWeb g

igGetWeb :: Int -> InterfGraph -> Web
igGetWeb i g = igIntToWeb g M.! i

-- | (dus, tomatch, extents)
type DUBuildFact = (S.Set DU, S.Set (Reg, Bool, NodePtr), S.Set (Reg, NodePtr))

duLattice :: DataflowLattice DUBuildFact
duLattice = DataflowLattice
            { fact_name = "du lattice"
            , fact_bot = (S.empty, S.empty, S.empty)
            , fact_join = add }
    where add _ (OldFact (oldDUs, oldUndefs, oldExtents)) (NewFact (newDUs, newUndefs, newExtents))
              = (ch, (dus', undefs', extents'))
              where dus' = S.union oldDUs newDUs
                    undefs' = S.union oldUndefs newUndefs
                    extents' = S.union oldExtents newExtents
                    bigger = (>) `on` S.size
                    ch = changeIf (undefs' `bigger` oldUndefs
                                   || dus' `bigger` oldDUs
                                   || extents' `bigger` newExtents)

duTransfer :: BwdTransfer (PNode Asm) DUBuildFact
duTransfer = mkBTransfer3 fe fm fx
    where fe :: (PNode Asm) C O -> DUBuildFact -> DUBuildFact
          fe (PNode l n) f
              = handle l False S.empty (getAliveDead n) (getPinned n) (getFixed n) f
          fm :: (PNode Asm) O O -> DUBuildFact -> DUBuildFact
          fm (PNode l n@(Spill{})) f
              = handle l True S.empty (getAliveDead n) (getPinned n) (getFixed n) f
          fm (PNode l n@(Reload{})) f
              = handle l True S.empty (getAliveDead n) (getPinned n) (getFixed n) f
          fm (PNode l n@(MovIRMtoR _ (IRM_R _) _)) f
              = handle l False (S.singleton l) (getAliveDead n) (getPinned n) (getFixed n) f
          fm (PNode l n) f
              = handle l False S.empty (getAliveDead n) (getPinned n) (getFixed n) f
          fx :: (PNode Asm) O C -> FactBase DUBuildFact -> DUBuildFact
          fx (PNode l n) fb
              = handle l False S.empty (getAliveDead n) (getPinned n) (getFixed n)
                (joinOutFacts duLattice n fb)
          
          handle :: NodePtr -> Bool -> S.Set NodePtr -> AliveDead -> [Reg] -> ([Reg], [Reg]) -> DUBuildFact 
                 -> DUBuildFact
          handle l sr mr (uses, defs) pinned (fixedUses, fixedDefs) (dus, tomatch, extents)
              = let withdef d = S.map makeDU rps
                        where rps = S.filter (\(reg, fixed, ptr) -> reg == d) tomatch
                              makeDU (reg, fixed, ptr)
                                  = DU reg sr mr (fixed || reg `elem` fixedDefs) l (ptrs reg) ptr
                    -- takes the NodePtrs from the current extents for a given register
                    ptrs r = S.map snd $ S.filter (\(reg, ptr) -> reg == r) extents
                    -- we can remove things which have been defined
                    tomatch' = S.filter (\(reg, fixed, ptr) -> reg `notElem` defs) tomatch
                    -- we want to add the used things to the tomatch list
                    dtomatch = S.fromList $ map (\r -> (r, r `elem` fixedUses, l)) uses
                    -- we add entries for things which are defined but
                    -- not used so caller-saved registers work
                    ddvirtused = S.fromList [DUv reg sr (reg `elem` fixedDefs) l
                                            | reg <- defs, reg `S.notMember` matchregs]
                    matchregs = S.map (\(reg, fixed, ptr) -> reg) tomatch
                    -- these are the matched definitions to put in the
                    -- dus set
                    ddu = S.unions $ map withdef defs
                    -- some variables are "pinned" across use/def boundaries
                    dduPinned = S.fromList $ map (\reg -> DU reg False S.empty False l S.empty l) pinned
                    alive = S.map fst extents
                    -- we clear the extents list of things which have been defined
                    extents' = S.filter (\(reg, ptr) -> reg `notElem` defs) extents
                    -- and extend the list for those which are still there
                    dextents = S.map (\(reg, fixed, ptr) -> (reg, l)) tomatch'
                               `S.union` (S.fromList $ map (\reg -> (reg, l)) pinned)
                in ( S.unions [dus, ddu, dduPinned, ddvirtused]
                   , tomatch' `S.union` dtomatch
                   , extents' `S.union` dextents )

duPass :: Monad m => BwdPass m (PNode Asm) DUBuildFact
duPass = BwdPass
         { bp_lattice = duLattice
         , bp_transfer = duTransfer
         , bp_rewrite = noBwdRewrite }

collectDU :: [Label] -> Graph (PNode Asm) C C -> M.Map Label (S.Set DU)
collectDU mlabels graph
    = M.fromList $ map (\l -> (l, getDUs $ fromJust $ lookupFact l f)) mlabels
      where f :: FactBase DUBuildFact
            f = I.runGM $ evalStupidFuelMonad getf 2222222
            getf :: RM (FactBase DUBuildFact)
            getf = do (_, f, _) <- analyzeAndRewriteBwd
                                   duPass
                                   (JustC mlabels)
                                   graph
                                   mapEmpty
                      return f
            getDUs (a, b, c) = a

collectWebs :: S.Set DU -> [Web]
collectWebs dus = iteration' webs webs
    where webs = map duToWeb (S.toList dus)
          duToWeb du@(DU r sr mr fixed d ex u)
              = Web r sr mr fixed (S.singleton du) (S.singleton d) ex (S.singleton u)
          duToWeb du@(DUv r sr fixed d)
              = Web r sr S.empty fixed (S.singleton du) (S.singleton d) S.empty S.empty
          wToCoalesce (Web r1 sr1 mr1 fixed1 dus1 ds1 ex1 us1) (Web r2 sr2 mr2 fixed2 dus2 ds2 ex2 us2)
              = r1 == r2 && (not (S.null $ ds1 `S.intersection` ds2)
                             || not (S.null $ us1 `S.intersection` us2))
          wUnion (Web r1 sr1 mr1 fixed1 dus1 ds1 ex1 us1) (Web r2 sr2 mr2 fixed2 dus2 ds2 ex2 us2)
              = Web 
                { webReg = r1 
                , webSpilled = sr1 || sr2
                , webMoveNodes = mr1 `S.union` mr2
                , webFixed = fixed1 || fixed2
                , webDUs = dus1 `S.union` dus2
                , webDefs = ds1 `S.union` ds2 
                , webExtent = ex1 `S.union` ex2 
                , webUses = us1 `S.union` us2 }
          iteration'' w webs
              = let (int, nint) = partition (wToCoalesce w) webs
                in case length int of
                     1 -> Nothing
                     _ -> Just $ (foldl1 wUnion int):nint
          iteration' [] webs = webs
          iteration' (w:tocheck) webs
              = case iteration'' w webs of
                  Nothing -> iteration' tocheck webs
                  Just webs' -> iteration' webs' webs'

makeInterfGraph :: [Web] -> RRFact -> InterfGraph
makeInterfGraph webs rrmoves = trace ("mkAdjs " ++ show mkAdjs) $ InterfGraph intToWebMap augAdjs rrmoves
    where intToWeb = zip [0..] webs
          intToWebMap = M.fromList intToWeb
          webToInt = zip webs [0..]
          webToIntMap = M.fromList webToInt
          mkAdj i w = S.fromList $ do
                        (j, w') <- intToWeb
                        guard $ i /= j
                        guard $ wInterf w w'
                        return j
          mkAdjs = M.fromList $ do
                     (i, w) <- intToWeb
                     return (i, mkAdj i w)
          -- | This is a map from the web number of fixed webs to a
          -- list of all the web numbers webs with that same register
          -- interfere with.  This helps make it appear like the webs
          -- for a particular fixed register are all one big web.
          fixedClasses :: M.Map Int [Int]
          fixedClasses = M.fromList [(i, S.toList $ combinedFixed M.! (webReg w))
                                    | (i, w) <- intToWeb, webFixed w]
          -- | This is a map from fixed webs to their adjacency lists.
          fixedWebAdjs :: M.Map Web (S.Set Int)
          fixedWebAdjs = M.map (mkAdjs M.!) $ M.filterWithKey (\k v -> webFixed k) webToIntMap
          -- | This is a mapping from fixed registers to the union
          -- of all of the webs those registers interfere with.
          combinedFixed :: M.Map Reg (S.Set Int)
          combinedFixed = M.mapKeysWith S.union webReg fixedWebAdjs
          
          augAdjs :: M.Map Int (S.Set Int)
          augAdjs = M.mapWithKey f mkAdjs
              where f k v
                        | webFixed web = case M.lookup (webReg web) combinedFixed of
                                           Just adjs -> v `S.union` adjs
                                           Nothing -> v
                        | otherwise = S.fromList $ do i <- S.toList v
                                                      M.findWithDefault [i] i fixedClasses
                        where web = intToWebMap M.! k

getRegRegMoves :: [Label] -> Graph (PNode Asm) C C -> M.Map Label RRFact
getRegRegMoves mlabels graph
    = M.fromList $ map (\l -> (l, fromJust $ lookupFact l facts)) mlabels
    where rrLattice :: DataflowLattice RRFact
          rrLattice = DataflowLattice
                      { fact_name = "rrLatice"
                      , fact_bot = S.empty
                      , fact_join = add }
              where add _ (OldFact s1) (NewFact s2) = (ch, s')
                        where s' = S.union s1 s2
                              ch = changeIf $ S.size s' > S.size s1
          rrTransfer :: BwdTransfer (PNode Asm) RRFact
          rrTransfer = mkBTransfer3 fe fm fx
              where fe :: PNode Asm C O -> RRFact -> RRFact
                    fe _ f = f
                    fm :: PNode Asm O O -> RRFact -> RRFact
                    fm (PNode l (MovIRMtoR _ (IRM_R sreg) dreg)) f
                        = S.insert (l, sreg, dreg) f
                    fm _ f = f
                    fx :: PNode Asm O C -> FactBase RRFact -> RRFact
                    fx n fs = joinOutFacts rrLattice n fs
          rrPass :: Monad m => BwdPass m (PNode Asm) RRFact
          rrPass = BwdPass
                   { bp_lattice = rrLattice
                   , bp_transfer = rrTransfer
                   , bp_rewrite = noBwdRewrite }
          doRR :: RM (FactBase RRFact)
          doRR = do (_, f, _) <- analyzeAndRewriteBwd
                                 rrPass
                                 (JustC mlabels)
                                 graph
                                 mapEmpty
                    return f
          facts :: FactBase RRFact
          facts = I.runGM $ evalStupidFuelMonad doRR 2222222

makeInterfGraphs :: [Label] -> Graph (PNode Asm) C C -> InterfGraphs
makeInterfGraphs mlabels pg = interfgraphs
    where dus = collectDU mlabels pg
          webs = M.map collectWebs dus
          rrfacts = getRegRegMoves mlabels pg
          interfgraphs = M.fromList $
                         map (\l -> (l, makeInterfGraph (webs M.! l) (rrfacts M.! l))) mlabels
          
data RWorklists = RWorklists
    { wInterfGraph :: InterfGraph
      
      -- Every web is in exactly one of the following:
    , wSpillWorklist :: [Int] -- ^ high-degree webs
    , wFreezeWorklist :: [Int] -- ^ low-degree move-related webs
    , wSimplifyWorklist :: [Int] -- ^ list of low-degree non-move-related webs
    , wSpilledWebs :: [Int] -- ^ webs marked for spilling
    , wCoalescedWebs :: S.Set Int -- ^ webs that have been coalesced
    , wColoredWebs :: M.Map Int X86Reg -- ^ webs successfully colored
    , wSelectStack :: [Int] -- ^ stack containing temporaries removed from the graph
      
    , wCoalescedAlias :: M.Map Int Int -- ^ when (u,v) coalesced and v
                                       -- is in coalesced webs, then
                                       -- wCoalescedAlias[v]==u
      
    , wDegrees :: M.Map Int Int -- ^ web to degree mapping
      
      -- Every move is in exactly one of the following
    , wWorklistMoves :: S.Set NodePtr -- ^ moves enabled for possible coalescing
    , wCoalescedMoves :: [NodePtr] -- ^ moves that have been coalesced
    , wConstrainedMoves :: [NodePtr] -- ^ moves whose source and target interfere
    , wFrozenMoves :: [NodePtr] -- ^ moves that will no longer be considered for coalescing
    , wActiveMoves :: S.Set NodePtr -- ^ moves not yet ready for coalescing
      
    , wMoves :: M.Map NodePtr [Int] -- ^ a map from nodes to web ids
    }
                  deriving Show

initWorklists :: InterfGraph -> S.Set NodePtr -> M.Map NodePtr [Int] -> M.Map Int Int
              -> RWorklists
initWorklists g wm moves deg = RWorklists
    { wInterfGraph = g
    , wSpillWorklist = []
    , wFreezeWorklist = []
    , wSimplifyWorklist = []
    , wSpilledWebs = []
    , wCoalescedWebs = S.empty
    , wColoredWebs = M.empty
    , wSelectStack = []
    , wCoalescedAlias = M.empty
    , wDegrees = deg
    , wWorklistMoves = wm
    , wCoalescedMoves = []
    , wConstrainedMoves = []
    , wFrozenMoves = []
    , wActiveMoves = S.empty
    , wMoves = moves
    }

-- | Updates webMoveNodes to the given value for the web id
updateWebMoves' :: S.Set NodePtr -> Int -> RWorklists -> RWorklists
updateWebMoves' s i wl
    = wl { wInterfGraph = g { igIntToWeb = M.insert i web' $ igIntToWeb g }}
    where g = wInterfGraph wl
          web = igIntToWeb g M.! i
          web' = web { webMoveNodes = s }

getWebMoves' :: Int -> RWorklists -> S.Set NodePtr
getWebMoves' i wl = webMoveNodes $ igIntToWeb (wInterfGraph wl) M.! i

addToAdjList :: Int -> Int -> AM ()
addToAdjList u v =
    do g <- wInterfGraph `fmap` get
       let adjs = igAdjLists g
       when (u /= v && not (v `S.member` (adjs M.! u))) $ do
         degrees <- wDegrees `fmap` get
         modify $ \wl -> wl { wInterfGraph = addInterfEdge u v g
                            , wDegrees = inc u $ inc v $ degrees }
    where inc i m = M.adjust (+1) i m
         
-- | The allocator monad
type AM = State RWorklists

pushSelect :: Int -> AM ()
pushSelect i = modify $ \wl -> wl { wSelectStack = i:(wSelectStack wl) }

popSelect :: AM Int
popSelect =  do wl@(RWorklists { wSelectStack = i:is }) <- get
                put $ wl { wSelectStack = is }
                return i


-- | Takes a web id and gives the current list of adjacent web ids. "Adjacent"
adjacentWebs :: Int -> AM (S.Set Int)
adjacentWebs i =
  do g <- wInterfGraph `fmap` get
     select <- (S.fromList . wSelectStack) `fmap` get
     coalesced <- wCoalescedWebs `fmap` get
     return $ (igAdjLists g M.! i) S.\\ (select `S.union` coalesced)

-- | Takes a web id and gives the current list of "move-related" webs. "NodeMoves"
webMoves :: Int -> AM (S.Set NodePtr)
webMoves i = 
    do wmoves <- getWebMoves' i `fmap` get
       actives <- wActiveMoves `fmap` get
       worklist <- wWorklistMoves `fmap` get
       return $ wmoves `S.intersection` (actives `S.union` worklist)

-- | Takes a web id and tells whether it's "move-related"
moveRelated :: Int -> AM Bool
moveRelated i = (not . S.null) `fmap` webMoves i

makeWorklists :: InterfGraph -> RWorklists
makeWorklists g = iter (igWebIDs g) (initWorklists g initMoves moves makeDegrees) 
    where iter [] wlists = wlists
          iter (i:is) wlists
              | webDegree i g >= numUsableRegisters
                  = iter is (wlists { wSpillWorklist = i:(wSpillWorklist wlists) })
              | evalState (moveRelated i) wlists
                  = iter is (wlists { wFreezeWorklist = i:(wFreezeWorklist wlists) })
              | otherwise
                  = iter is (wlists { wSimplifyWorklist = i:(wSimplifyWorklist wlists) })
          initMoves = S.map (\(l,_,_) -> l) $ igRRMoves g
          moves = M.fromList $ map (\(l,_,_) -> (l, websWithLabel l)) $ S.toList $ igRRMoves g
          websWithLabel l = M.keys $ M.filter cond $ igIntToWeb g
              where cond w = l `S.member` (webDefs w) || l `S.member` (webUses w)
          makeDegrees = M.fromList $ map (\i -> (i, webDegree i g)) (igWebIDs g)

-- | "main"
doRegAlloc :: SpillLocSupply -> Label -> Graph Asm C C -> Graph Asm C C
doRegAlloc spillLocs mlabel graph
    = let pg = toPGraph graph
          dus = collectDU [mlabel] pg
          webs = collectWebs (dus M.! mlabel)
          rrfacts = getRegRegMoves [mlabel] pg
          interfgraph = makeInterfGraph webs (rrfacts M.! mlabel)
          initState = makeWorklists interfgraph
          spilledNodes = evalState (return pg) initState
          -- | runs simplify/coalesce/freeze/selectspill until work
          -- lists are empty
          mainLoop = do wl <- get
                        let mtodo = msum
                                    [ do guard $ not (null $ wSimplifyWorklist wl)
                                         return $ trace "simplify" simplify
                                    , do guard $ not (S.null $ wWorklistMoves wl)
                                         return $ trace "coalesce" coalesce
                                    , do guard $ not (null $ wFreezeWorklist wl)
                                         return $ trace "freeze" freeze
                                    , do guard $ not (null $ wSpillWorklist wl)
                                         return $ trace "selectSpill" selectSpill
                                    ]
                        case mtodo of
                          Just action -> do action
                                            mainLoop
                          Nothing -> return ()
          main = do trace ("interfgraph\n" ++ outputWebGraph interfgraph ++ "\nmainLoop") mainLoop
                    trace "assignColors" assignColors
                    spilledWebs <- wSpilledWebs `fmap` get
                    wl <- get
                    if trace ("\nspilledWebs: " ++ show spilledWebs ++ " colors: " ++ show (wColoredWebs wl) ++ "\n") $ not $ null spilledWebs
                       then let (spillLocs', graph') = insertSpills spillLocs pg wl
                            in return $ doRegAlloc spillLocs' mlabel graph'
                       else return $ trace ("done: " ++ show wl) $ rewriteGraph pg wl
      in evalState main (trace ("initState: " ++ show initState) initState)

insertSpills :: SpillLocSupply -> Graph (PNode Asm) C C -> RWorklists 
             -> (SpillLocSupply, Graph Asm C C)
insertSpills spillLocs pg wl = trace ("insertSpills: " ++ show toSpill ++ show toReload) (spillLocs', graph')
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
          fe (PNode l n) = mkFirst n <*> mkMiddles (map genSpill defined')
              where (used, defined) = getAliveDead n
                    defined' = filter (\d -> (l, d) `M.member` toSpill) defined
                    genSpill reg = Spill noPosition reg (toSpill M.! (l, reg))
          
          fm :: PNode Asm O O -> Graph Asm O O
          fm (PNode l n) = trace (show l ++ show n ++ show used ++ show used' ++ show defined ++ show defined') $ mkMiddles $ map genReload used' ++ [n] ++ map genSpill defined'
              where (used, defined) = getAliveDead n
                    used' = filter (\u -> (l, u) `M.member` toReload) used
                    defined' = filter (\d -> (l, d) `M.member` toSpill) defined
                    genReload reg = Reload noPosition (toReload M.! (l, reg)) reg
                    genSpill reg = Spill noPosition reg (toSpill M.! (l, reg))
          
          fx :: PNode Asm O C -> Graph Asm O C
          fx (PNode l n) = mkMiddles (map genReload used') <*> mkLast n
              where (used, defined) = getAliveDead n
                    used' = filter (\u -> (l, u) `M.member` toReload) used
                    genReload reg = Reload noPosition (toReload M.! (l, reg)) reg
          
          spillLocs' = drop (length $ wSpilledWebs wl) spillLocs
          slmap = M.fromList $ zip (wSpilledWebs wl) spillLocs
          
          intToWeb = M.toList $ igIntToWeb (wInterfGraph wl)
          spilledWebs = do (i, w) <- intToWeb
                           let i' = getAlias' i wl
                           guard $ i' `elem` wSpilledWebs wl
                           return (w, slmap M.! i')
          
          toReload = M.fromList $ do (w, sl) <- spilledWebs
                                     u <- S.toList $ webUses w
                                     return $ ((u, webReg w), sl)
          toSpill = M.fromList $ do (w, sl) <- spilledWebs
                                    d <- S.toList $ webDefs w
                                    return $ ((d, webReg w), sl)

rewriteGraph :: Graph (PNode Asm) C C -> RWorklists -> Graph Asm C C
rewriteGraph pg wl = trace ("rewriteGraph: " ++ show usesColorMap ++ show defsColorMap) graph'
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
          fm (PNode l n) = mkMiddle $ mapAsm fs fd n
              where fs r = fromMaybe r $ M.lookup (l, r) usesColorMap
                    fd r = fromMaybe r $ M.lookup (l, r) defsColorMap
          
          fx :: PNode Asm O C -> Graph Asm O C
          fx (PNode l n) = mkLast n
          
          intToWeb = M.toList $ igIntToWeb (wInterfGraph wl)
          usesColorMap = M.fromList $ do (i, w) <- intToWeb
                                         u <- S.toList $ webUses w
                                         case M.lookup i (wColoredWebs wl) of
                                           Just r -> return ((u, webReg w), MReg r)
                                           Nothing -> mzero
          defsColorMap = M.fromList $ do (i, w) <- intToWeb
                                         d <- S.toList $ webDefs w
                                         case M.lookup i (wColoredWebs wl) of
                                           Just r -> return ((d, webReg w), MReg r)
                                           Nothing -> mzero


-- | "Simplify"
simplify :: AM ()
simplify = do u <- selectSimplify
              wl <- get
              let web = igGetWeb u (wInterfGraph wl)
              trace ("pushSelect " ++ show u ++ " = " ++ show (webReg web)) $ pushSelect u
              adjs <- adjacentWebs u
              mapM_ decrementDegree (S.toList adjs)

-- | Chooses the web to simplify
selectSimplify :: AM Int
selectSimplify =
  do wl@(RWorklists { wSimplifyWorklist = choices }) <- get
     x <- choose choices
     put $ wl { wSimplifyWorklist = delete x choices }
     return x
    where choose (x:xs) =
              do return x

 -- | Decrements the degree of the web in the
 -- worklist. "DecrementDegree"
decrementDegree :: Int -> AM ()
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
enableMoves :: Int -> AM ()
enableMoves i = do moves <- S.toList `fmap` webMoves i
                   forM_ moves $ \m -> do
                     activeMoves <- wActiveMoves `fmap` get
                     when (m `S.member` activeMoves) $
                          do modify $ \wl -> wl { wActiveMoves = S.delete m activeMoves
                                                , wWorklistMoves = S.insert m (wWorklistMoves wl) }

-- | "Coalesce"
coalesce :: AM ()
coalesce = do m <- selectMove
              [x, y] <- (\wl -> wMoves wl M.! m) `fmap` get
              [x, y] <- mapM getAlias [x, y]
              intToWeb <- (igIntToWeb . wInterfGraph) `fmap` get
              let yFixed = webFixed $ intToWeb M.! y
              let (u, v) = if yFixed then (y, x) else (x, y)
              -- Invariant: if either u,v is fixed, then u is fixed.
              wl <- get
              let uweb = intToWeb M.! u
                  vweb = intToWeb M.! v
                  adjuv = S.member v $ (igAdjLists $ wInterfGraph wl) M.! u
              adjacentu <- adjacentWebs u
              adjacentv <- adjacentWebs v
              okadjv <- and `fmap` mapM (\t -> ok t u) (S.toList adjacentv)
              conserv <- conservative $ adjacentu `S.union` adjacentv
              cond $
                [
                 ( webReg uweb == webReg vweb
                 , do modify $ \wl -> wl { wCoalescedMoves = m:(wCoalescedMoves wl) }
                      addWorklist u
                 )
                ,( webFixed vweb || adjuv
                 , do modify $ \wl -> wl { wConstrainedMoves = m:(wConstrainedMoves wl) }
                      addWorklist u
                      addWorklist v
                 )
                ,( conserv
                 , do modify $ \wl -> wl { wCoalescedMoves = m:(wCoalescedMoves wl) }
                      combine u v
                      addWorklist u
                 )
                ,( True
                 , do modify $ \wl -> wl { wActiveMoves = S.insert m $ wActiveMoves wl }
                 )
                ]
    where cond :: Monad m => [(Bool, m ())] -> m ()
          cond opts = fromMaybe (return ()) $ msum $ map (\(b,m) -> guard b >> return m) opts
          
          ok t r = do wl <- get
                      let deg = wDegrees wl M.! t
                          fixed = webFixed (igIntToWeb (wInterfGraph wl) M.! t)
                          adjtr = S.member r (igAdjLists (wInterfGraph wl) M.! t)
                      return $ deg < numUsableRegisters || fixed || adjtr
          conservative nodes = conservative' 0 (S.toList nodes)
              where conservative' k [] = return $ k < numUsableRegisters
                    conservative' k (n:ns) =
                        do wl <- get
                           let deg = wDegrees wl M.! n
                           case deg >= numUsableRegisters of
                             True -> conservative' (k+1) ns
                             False -> conservative' k ns
          
          addWorklist :: Int -> AM ()
          addWorklist u =
              do wl <- get
                 let uweb = igIntToWeb (wInterfGraph wl) M.! u
                     deg = wDegrees wl M.! u
                     fixed = webFixed uweb
                 moverelated <- moveRelated u
                 when (not moverelated && deg < numUsableRegisters) $ do
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
combine :: Int -> Int -> AM ()
combine u v =
    do wl <- get
       case v `elem` wFreezeWorklist wl of
         True -> modify $ \wl -> wl { wFreezeWorklist = delete v $ wFreezeWorklist wl }
         False -> modify $ \wl -> wl { wSpillWorklist = delete v $ wSpillWorklist wl }
       modify $ \wl -> wl { wCoalescedWebs = S.insert v $ wCoalescedWebs wl
                          , wCoalescedAlias = M.insert v u $ wCoalescedAlias wl }
       webmovesu <- getWebMoves' u `fmap` get
       webmovesv <- getWebMoves' v `fmap` get
       modify $ updateWebMoves' (webmovesu `S.union` webmovesv) u
       adjv <- S.toList `fmap` adjacentWebs v
       forM_ adjv $ \t -> do
         addToAdjList t u
         decrementDegree t
       wl <- get
       let d = wDegrees wl M.! u
       when (d >= numUsableRegisters
             && u `elem` wFreezeWorklist wl
             && u `notElem` wSpillWorklist wl) $ do
         modify $ \wl -> wl { wFreezeWorklist = delete u $ wFreezeWorklist wl
                            , wSpillWorklist = u:(wSpillWorklist wl) }

-- | "GetAlias"
getAlias :: Int -> AM Int
getAlias i = (getAlias' i) `fmap` get

getAlias' :: Int -> RWorklists -> Int
getAlias' i wl = case i `S.member` wCoalescedWebs wl of
                   True -> getAlias' (wCoalescedAlias wl M.! i) wl
                   False -> i

-- | "Freeze"
freeze :: AM ()
freeze = do u <- selectFreeze
            modify $ \wl -> wl { wFreezeWorklist = delete u $ wFreezeWorklist wl
                               , wSimplifyWorklist = u:(wSimplifyWorklist wl) }
            freezeMoves(u)
    where selectFreeze = do (u:_) <- wFreezeWorklist `fmap` get
                            return u

-- | "FreezeMoves"
freezeMoves :: Int -> AM ()
freezeMoves u = do wmoves <- webMoves u
                   wl <- get
                   let wmoves' = map (\l -> (l, wMoves wl M.! l)) $ S.toList wmoves
                   forM_ (filter (elem u . snd) wmoves') $ \(m,uv) -> do
                     let [v] = delete u uv
                     modify $ \wl ->
                       case m `S.member` wActiveMoves wl of
                         True -> wl { wActiveMoves = S.delete m $ wActiveMoves wl }
                         False -> wl { wWorklistMoves = S.delete m $ wWorklistMoves wl }
                     modify $ \wl -> wl { wFrozenMoves = m:(wFrozenMoves wl) }
                     wmv <- webMoves v
                     degv <- (\wl -> wDegrees wl M.! v) `fmap` get
                     when (S.null wmv && degv < numUsableRegisters) $ do
                       modify $ \wl -> wl { wFreezeWorklist = delete v $ wFreezeWorklist wl
                                          , wSimplifyWorklist = v:(wSimplifyWorklist wl) }


-- | "SelectSpill"
selectSpill :: AM ()
selectSpill = do m <- chooseSpill
                 modify $ \wl -> wl { wSpillWorklist = delete m $ wSpillWorklist wl
                                    , wSimplifyWorklist = m:(wSimplifyWorklist wl) }
                 freezeMoves m
    where chooseSpill =
              do wl <- get
                 let spillList = wSpillWorklist wl
                 let costs = map (\i -> (i, cost wl i)) spillList
                 return $ trace ("costs: " ++ show costs) $ fst $ maximumBy (compare `on` snd) costs
          cost wl i = let web = igGetWeb i $ wInterfGraph wl
                          deg = wDegrees wl M.! i
                          dus = S.toList $ webDUs web
                          len (DU {duExtent = ext}) = S.size ext
                          len (DUv{}) = 0
                          score = deg * sum (map len dus) `div` (1 + (S.size $ webUses web))
                      in score

-- | "AssignColors"
assignColors :: AM ()
assignColors = do emptyStack
                  wl <- get
                  forM_ (S.toList $ wCoalescedWebs (trace (outputWebGraph $ wInterfGraph wl) wl)) $ \n -> do
                    alias <- getAlias n
                    modify $ \wl -> wl { wColoredWebs = M.insert n (wColoredWebs wl M.! alias) 
                                                        (wColoredWebs wl) }
    where emptyStack :: AM ()
          emptyStack
              = do wl <- get
                   when (not $ null $ wSelectStack wl) $ do
                     n <- popSelect
                     web <- (igGetWeb n . wInterfGraph) `fmap` get
                     wl <- get
                     okColors <- if webFixed web then return [x86reg $ webReg web] else determineColors n
                     case trace (show n ++ " " ++ show (webReg web) ++ " okColors: " ++ show okColors ++ " " ++ show (igAdjLists (wInterfGraph wl) M.! n) ++ " " ++ show (wColoredWebs wl)) okColors of
                       [] -> modify $ \wl -> wl { wSpilledWebs = n:(wSpilledWebs wl) }
                       (c:_) -> modify $ \wl ->
                                   wl { wColoredWebs = M.insert n c (wColoredWebs wl) }
                     emptyStack
          x86reg (MReg r) = r
          x86reg r = error $ show r ++ " is not a machine register but is associated with a fixed web."
          determineColors :: Int -> AM [X86Reg]
          determineColors n = do wl <- get
                                 let adj = S.toList $ igAdjLists (wInterfGraph wl) M.! n
                                 adj' <- mapM getAlias adj
                                 allcolored <- wColoredWebs `fmap` get
                                 let colored = filter (`M.member` allcolored) adj'
                                     usedColors = map (allcolored M.!) colored
                                     ok = usableRegisters \\ usedColors
                                 return ok

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
                    wf = if webFixed web then "fixed" else "free"
                    wd = show $ webDefs web
                    we = show $ webExtent web
                    wu = show $ webUses web
          webs = M.toList $ igIntToWeb ig
          g = igAdjLists ig



-- | Gets the registers which are "pinned" by the instruction.  That
-- is, those registers which are both used and defined by the
-- instruction, and two registers cannot be used instead.  For
-- instance, %rax in "addq $5, %rax".
getPinned :: forall e x. Asm e x -> [Reg]
getPinned expr
    = case expr of
        Label{} -> []
        Spill _ r d -> []
        Reload _ s r -> []
        MovIRMtoR _ irm r -> []
        MovIRtoM _ ir m -> []
        Mov64toR _ i r -> []
        CMovRMtoR _ _ rm r -> [r]
        Enter _ _ _ _ -> []
        Leave{} -> [MReg RSP]
        Call p nargs i -> []
        Callout p nargs i -> []
        Ret p rets -> []
        RetPop p rets num -> []
        ExitFail{} -> []
--        Realign{} -> []
--        Unrealign{} -> []
        Lea p m r -> []
        Push p irm -> []
        Pop p rm -> []
        Jmp{} -> []
        JCond{} -> []
        ALU_IRMtoR _ _ irm r -> [r]
        ALU_IRtoM _ _ ir m -> []
        Cmp _ ir rm -> []
        Test _ ir rm -> []
        Inc _ rm -> snd $ getRDst rm
        Dec _ rm -> snd $ getRDst rm
        Neg _ rm -> snd $ getRDst rm
        IMulRAX _ rm -> [MReg RAX]
        IMulRM _ rm r -> [r]
        IMulImm _ i rm r -> []
        IDiv _ rm -> [MReg RDX, MReg RAX]
        Cqo _ -> []
        Shl _ _ rm -> snd $ getRDst rm
        Shr _ _ rm -> snd $ getRDst rm
        Sar _ _ rm -> snd $ getRDst rm
        Nop _ -> []


-- | Gets those registers which are fixed by the instruction, such as
-- %rax for ret.
getFixed :: forall e x. Asm e x -> ([Reg], [Reg]) -- ^ (used, defined)
getFixed expr
    = case expr of
        Label{} -> noFixed
        Spill _ r d -> noFixed
        Reload _ s r -> noFixed
        MovIRMtoR _ irm r -> noFixed
        MovIRtoM _ ir m -> noFixed
        Mov64toR _ i r -> noFixed
        CMovRMtoR _ _ rm r -> noFixed
        Enter _ _ i _ -> ([], x ++ map MReg A.calleeSaved ++ [MReg RSP]) 
            where x = map MReg (catMaybes $ take i argOrder)
        Leave{} -> ([MReg RSP], [MReg RSP])
        Call p nargs i -> (x, [MReg RAX]) <+> ([MReg RSP], map MReg A.callerSaved ++ [MReg RSP])
            where x = map MReg (catMaybes $ take nargs argOrder)
        Callout p nargs i -> (x ++ [MReg RAX], [MReg RAX])
                             <+> ([MReg RSP], map MReg A.callerSaved ++ [MReg RSP])
            where x = map MReg (catMaybes $ take nargs argOrder)
        Ret p rets -> (if rets then [MReg RAX] else [], []) <+> (map MReg A.calleeSaved ++ [MReg RSP], [])
        RetPop p rets num -> (if rets then [MReg RAX] else [], []) <+> (map MReg A.calleeSaved ++ [MReg RSP], [])
        ExitFail{} -> noFixed
--        Realign{} -> []
--        Unrealign{} -> []
        Lea p m r -> noFixed
        Push p irm -> noFixed
        Pop p rm -> ([MReg RSP], [MReg RSP])
        Jmp{} -> noFixed
        JCond{} -> noFixed
        ALU_IRMtoR _ _ irm r -> noFixed
        ALU_IRtoM _ _ ir m -> noFixed
        Cmp _ ir rm -> noFixed
        Test _ ir rm -> noFixed
        Inc _ rm -> noFixed
        Dec _ rm -> noFixed
        Neg _ rm -> noFixed
        IMulRAX _ rm -> ([MReg RAX], [MReg RAX, MReg RDX])
        IMulRM _ rm r -> noFixed
        IMulImm _ i rm r -> noFixed
        IDiv _ rm -> ([MReg RDX, MReg RAX], [MReg RDX, MReg RAX])
        Cqo _ -> ([MReg RAX], [MReg RDX])
        Shl _ _ rm -> noFixed
        Shr _ _ rm -> noFixed
        Sar _ _ rm -> noFixed
        Nop _ -> noFixed
      where noFixed = ([], [])
