{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

-- | We kind of follow "Iterated Register Coalescing" by Lal George
-- and Andrew Appel.
module RegisterAllocator where 

import qualified Data.Map as M
import Assembly
import qualified Assembly as A
import CodeGenerate
import qualified IR as I
import Dataflow
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
regAlloc (LowIRRepr fields strs meths graph)
    = do --graph'' <- evalStupidFuelMonad (collectSpill mlabels graph') 22222222
         return $ LowIRRepr fields strs meths graph'
      where GMany _ body _ = graph
            pg = toPGraph graph
            interfgraphs = makeInterfGraphs mlabels pg
            webs = M.map makeWorklists interfgraphs
            graph' = error $ join (map (show . snd) $ M.toList webs) --intercalate "\n" $ map snd (M.toList webs)
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
            mlabels = map I.methodEntry meths

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
             , duMoveNodes :: S.Set NodePtr
             , duFixed :: Bool
             , duDef :: NodePtr
             , duExtent :: S.Set NodePtr
             , duUse :: NodePtr }
        | DUv { duReg :: Reg
              , duFixed :: Bool
              , duDef :: NodePtr } -- ^ Represents a register which is
                                   -- defined but not used.  It should
                                   -- still be given a chance to
                                   -- interfere!
          deriving (Eq, Ord, Show)
data Web = Web { webReg :: Reg
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
    { igWebToInt :: M.Map Web Int
    , igIntToWeb :: M.Map Int Web
    , igAdjLists :: M.Map Int (S.Set Int)
    , igRRMoves :: RRFact
    }
                   deriving Show

type InterfGraphs = M.Map Label InterfGraph

-- | Checks whether two webs interfere
wInterf :: Web -> Web -> Bool
wInterf (Web _ _ _ dus1 ds1 ex1 us1) (Web _ _ _ dus2 ds2 ex2 us2)
    = (S.union ds1 ex1 `ints` S.union ds2 ex2)
      || (S.union ex1 us1 `ints` S.union ex2 us2)
      where ints s1 s2 = not $ S.null $ s1 `S.intersection` s2

--removeWeb :: Int -> InterfGraph -> InterfGraph
--removeWeb i g = InterfGraph
--                { igWebToInt = M.filter (/= i) $ igWebToInt g
--                , igIntToWeb = M.filterWithKey (\k v -> k /= i) $ igIntToWeb g
--                , igAdjLists = M.map withoutI $ M.filterWithKey (\k v -> k /= i) $ igAdjLists g
--                }
--    where adj = igAdjLists g M.! i
--          withoutI a = S.delete i a

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
              = handle l S.empty (getAliveDead n) (getPinned n) (getFixed n) f
          fm :: (PNode Asm) O O -> DUBuildFact -> DUBuildFact
          fm (PNode l n@(MovIRMtoR _ (IRM_R _) _)) f
              = handle l (S.singleton l) (getAliveDead n) (getPinned n) (getFixed n) f
          fm (PNode l n) f
              = handle l S.empty (getAliveDead n) (getPinned n) (getFixed n) f
          fx :: (PNode Asm) O C -> FactBase DUBuildFact -> DUBuildFact
          fx (PNode l n) fb
              = handle l S.empty (getAliveDead n) (getPinned n) (getFixed n)
                (joinOutFacts duLattice n fb)
          
          handle :: NodePtr -> S.Set NodePtr -> AliveDead -> [Reg] -> ([Reg], [Reg]) -> DUBuildFact 
                 -> DUBuildFact
          handle l mr (uses, defs) pinned (fixedUses, fixedDefs) (dus, tomatch, extents)
              = let withdef d = S.map makeDU rps
                        where rps = S.filter (\(reg, fixed, ptr) -> reg == d) tomatch
                              makeDU (reg, fixed, ptr)
                                  = DU reg mr (fixed || reg `elem` fixedDefs) l (ptrs reg) ptr
                    -- takes the NodePtrs from the current extents for a given register
                    ptrs r = S.map snd $ S.filter (\(reg, ptr) -> reg == r) extents
                    -- we can remove things which have been defined
                    tomatch' = S.filter (\(reg, fixed, ptr) -> reg `notElem` defs) tomatch
                    -- we want to add the used things to the tomatch list
                    dtomatch = S.fromList $ map (\r -> (r, r `elem` fixedUses, l)) uses
                    -- we add entries for things which are defined but
                    -- not used so caller-saved registers work
                    ddvirtused = S.fromList [DUv reg (reg `elem` fixedDefs) l
                                            | reg <- defs, reg `S.notMember` matchregs]
                    matchregs = S.map (\(reg, fixed, ptr) -> reg) tomatch
                    -- these are the matched definitions to put in the
                    -- dus set
                    ddu = S.unions $ map withdef defs
                    -- some variables are "pinned" across use/def boundaries
                    dduPinned = S.fromList $ map (\reg -> DU reg S.empty False l S.empty l) pinned
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
          duToWeb du@(DU r mr fixed d ex u)
              = Web r mr fixed (S.singleton du) (S.singleton d) ex (S.singleton u)
          duToWeb du@(DUv r fixed d)
              = Web r S.empty fixed (S.singleton du) (S.singleton d) S.empty S.empty
          wToCoalesce (Web r1 mr1 fixed1 dus1 ds1 ex1 us1) (Web r2 mr2 fixed2 dus2 ds2 ex2 us2)
              = r1 == r2 && (not (S.null $ ds1 `S.intersection` ds2)
                             || not (S.null $ us1 `S.intersection` us2))
          wUnion (Web r1 mr1 fixed1 dus1 ds1 ex1 us1) (Web r2 mr2 fixed2 dus2 ds2 ex2 us2)
              = Web 
                { webReg = r1 
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
makeInterfGraph webs rrmoves = InterfGraph webToIntMap intToWebMap augAdjs rrmoves
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
    }
                  deriving Show

initWorklists :: InterfGraph -> S.Set NodePtr -> M.Map Int Int -> RWorklists
initWorklists g wm deg = RWorklists
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
    }

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
    do g <- wInterfGraph `fmap` get
       actives <- wActiveMoves `fmap` get
       worklist <- wWorklistMoves `fmap` get
       return $ webMoveNodes (igGetWeb i g)
                  `S.intersection` (actives `S.union` worklist)

-- | Takes a web id and tells whether it's "move-related"
moveRelated :: Int -> AM Bool
moveRelated i = (not . S.null) `fmap` webMoves i

makeWorklists :: InterfGraph -> RWorklists
makeWorklists g = iter (igWebIDs g) (initWorklists g initMoves makeDegrees) 
    where iter [] wlists = wlists
          iter (i:is) wlists
              | webDegree i g >= numUseableRegisters
                  = iter is (wlists { wSpillWorklist = i:(wSpillWorklist wlists) })
              | evalState (moveRelated i) wlists
                  = iter is (wlists { wFreezeWorklist = i:(wFreezeWorklist wlists) })
              | otherwise
                  = iter is (wlists { wSimplifyWorklist = i:(wSimplifyWorklist wlists) })
          initMoves = S.map (\(l,_,_) -> l) $ igRRMoves g
          makeDegrees = M.fromList $ map (\i -> (i, webDegree i g)) (igWebIDs g)

-- | "main"
doRegAlloc :: Label -> Graph (PNode Asm) C C -> Graph (PNode Asm) C C
doRegAlloc mlabel pg
    = let dus = collectDU [mlabel] pg
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
                                         return simplify
                                    , do guard $ not (S.empty $ wWorklistMoves wl)
                                         return coalesce
                                    , do guard $ not (null $ wFreezeWorklist wl)
                                         return freeze
                                    , do guard $ not (null $ wSpillWorklist wl)
                                         return selectSpill
                                    ]
                        case mtodo of
                          Just action -> do action
                                            mainLoop
                          Nothing -> return ()
          main = do mainLoop
                    assignColors
                    spilledWebs <- wSpilledWebs `fmap` get
                    if not $ null spilledWebs
                       then return $ doRegAlloc mlabel (rewriteProgram pg spilledWebs)
                       else return pg
      in evalState main initState

-- "Simplify"
simplify :: AM ()
simplify = do u <- selectSimplify
              pushSelect u
              adjs <- adjacentWebs u
              mapM_ decrementDegree (S.toList adjs)

-- | Chooses the web to simplify
selectSimplify :: AM Int
selectSimplify =
  do wl@(RWorklists { wSimplifyWorklist = choices }) <- get
     (x,xs) <- choose choices
     put $ wl { wSimplifyWorklist = xs }
     return x
    where choose (x:xs) =
              do return (x, xs)

 -- | Decrements the degree of the web in the worklist
decrementDegree :: Int -> AM ()
decrementDegree i =
    do wl <- get
       let d = wDegrees wl M.! i
       put $ wl { wDegrees = M.adjust (subtract 1) i (wDegrees wl) }
       when (d == numUseableRegisters) $ do
         enableMoves i
         adj <- S.toList `fmap` adjacentWebs i
         mapM_ enableMoves adj
         modify $ \wl -> wl { wSpillWorklist = delete i (wSpillWorklist wl) }
         mr <- moveRelated i
         case mr of
           True -> modify $ \wl -> wl { wFreezeWorklist = i:(wFreezeWorklist wl) }
           False -> modify $ \wl -> wl { wSimplifyWorklist = i:(wSimplifyWorklist wl) }

enableMoves :: Int -> AM ()
enableMoves i = do moves <- S.toList `fmap` webMoves i
                   forM_ moves $ \m -> do
                     activeMoves <- wActiveMoves `fmap` get
                     when (m `S.member` activeMoves) $
                          do modify $ \wl -> wl { wActiveMoves = S.delete m activeMoves
                                                , wWorklistMoves = S.insert m (wWorklistMoves wl) }
                                         

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

---
--- Aliveness/deadness (aka use/definition)
---


type AliveDead = ([Reg], [Reg])
class GetRegs x where
    getRSrc :: x -> AliveDead
    getRDst :: x -> AliveDead

emptyAD :: AliveDead
emptyAD = ([], [])

infixl 5 <+>

(<+>) :: AliveDead -> AliveDead -> AliveDead
(a1,d1) <+> (a2,d2) = (a1++a2, d1++d2)

instance GetRegs OperIRM where
    getRSrc (IRM_I _) = ([],[])
    getRSrc (IRM_R r) = getRSrc r
    getRSrc (IRM_M m) = getRSrc m
    getRDst (IRM_I _) = ([],[])
    getRDst (IRM_R r) = getRDst r
    getRDst (IRM_M m) = getRDst m
instance GetRegs OperIR where
    getRSrc (IR_I _) = ([],[])
    getRSrc (IR_R r) = getRSrc r
    getRDst (IR_I _) = ([],[])
    getRDst (IR_R r) = getRDst r
instance GetRegs OperRM where
    getRSrc (RM_R r) = getRSrc r
    getRSrc (RM_M m) = getRSrc m
    getRDst (RM_R r) = getRDst r
    getRDst (RM_M m) = getRDst m
instance GetRegs MemAddr where
    getRSrc (MemAddr br d i s)
        = (maybeToList br ++ maybeToList i, [])
    getRDst (MemAddr br d i s)
        = (maybeToList br ++ maybeToList i, [])
instance GetRegs Reg where
    getRSrc r = ([r],[])
    getRDst r = ([],[r])

map_IRM :: (Reg -> Reg) -> OperIRM -> OperIRM
map_IRM f (IRM_I i) = IRM_I i
map_IRM f (IRM_R r) = IRM_R $ f r
map_IRM f (IRM_M m) = IRM_M $ map_M f m

map_IR :: (Reg -> Reg) -> OperIR -> OperIR
map_IR f (IR_I i) = IR_I i
map_IR f (IR_R r) = IR_R $ f r

map_RM :: (Reg -> Reg) -> OperRM -> OperRM
map_RM f (RM_R r) = RM_R $ f r
map_RM f (RM_M m) = RM_M $ map_M f m

map_M :: (Reg -> Reg) -> MemAddr -> MemAddr
map_M f (MemAddr br d i s) = MemAddr (fmap f br) d (fmap f i) s

mapRR :: forall e x. (Reg -> Reg) -> Asm e x -> Asm e x
mapRR f a@(Label{}) = a
mapRR f (Spill pos r d) = Spill pos (f r) d
mapRR f (Reload pos s r) = Reload pos s (f r)
mapRR f (MovIRMtoR p irm r) = MovIRMtoR p (map_IRM f irm) (f r)
mapRR f (MovIRtoM p ir m) = MovIRtoM p (map_IR f ir) (map_M f m)
mapRR f (Mov64toR p i r) = Mov64toR p i (f r)
mapRR f (CMovRMtoR p fl rm r) = CMovRMtoR p fl (map_RM f rm) (f r)
mapRR f a@(Enter{}) = a
mapRR f a@(Leave{}) = a
mapRR f a@(Call{}) = a
mapRR f a@(Callout{}) = a
mapRR f a@(Ret{}) = a
mapRR f a@(RetPop{}) = a
mapRR f a@(ExitFail{}) = a
--mapRR f a@(Realign{}) = a
--mapRR f a@(Unrealign{}) = a
mapRR f (Lea p m r) = Lea p (map_M f m) (f r)
mapRR f (Push p irm) = Push p (map_IRM f irm)
mapRR f (Pop p rm) = Pop p (map_RM f rm)
mapRR f a@(Jmp{}) = a
mapRR f a@(JCond{}) = a
mapRR f (ALU_IRMtoR p op irm r) = ALU_IRMtoR p op (map_IRM f irm) (f r)
mapRR f (ALU_IRtoM p op ir m) = ALU_IRtoM p op (map_IR f ir) (map_M f m)
mapRR f (Cmp p ir rm) = Cmp p (map_IR f ir) (map_RM f rm)
mapRR f (Test p ir rm) = Test p (map_IR f ir) (map_RM f rm)
mapRR f (Inc p rm) = Inc p (map_RM f rm)
mapRR f (Dec p rm) = Dec p (map_RM f rm)
mapRR f (Neg p rm) = Neg p (map_RM f rm)
mapRR f (IMulRAX p rm) = IMulRAX p (map_RM f rm)
mapRR f (IMulRM p rm r) = IMulRM p (map_RM f rm) (f r)
mapRR f (IMulImm p i rm r) = IMulImm p i (map_RM f rm) (f r)
mapRR f (IDiv p rm) = IDiv p (map_RM f rm)
mapRR f (Cqo p) = Cqo p
mapRR f (Shl p i rm) = Shl p i (map_RM f rm)
mapRR f (Shr p i rm) = Shr p i (map_RM f rm)
mapRR f (Sar p i rm) = Sar p i (map_RM f rm)
mapRR f (Nop p) = Nop p

-- | Gets the registers which are used and defined (also known as
-- "alive" and "dead", respectively, because of backwards liveness
-- analysis).
getAliveDead :: forall e x. Asm e x -> AliveDead
getAliveDead expr
    = case expr of
        Label{} -> emptyAD
        Spill _ r d -> getRSrc r
        Reload _ s r -> getRDst r
        MovIRMtoR _ irm r -> getRSrc irm <+> getRDst r
        MovIRtoM _ ir m -> getRSrc ir <+> getRDst m
        Mov64toR _ i r -> getRDst r
        CMovRMtoR _ _ rm r -> getRSrc rm <+> getRSrc r <+> getRDst r
        Enter _ _ i _ -> ([], x) <+> ([], map MReg A.calleeSaved ++ [MReg RSP])
                where x = map MReg (catMaybes $ take i argOrder)
        Leave{} -> ([MReg RSP], [MReg RSP])
        Call p nargs i -> (x, [MReg RAX]) <+> ([MReg RSP], map MReg A.callerSaved ++ [MReg RSP])
                where x = map MReg (catMaybes $ take nargs argOrder)
        Callout p nargs i -> (x ++ [MReg RAX], [MReg RAX]) <+> ([MReg RSP], map MReg A.callerSaved ++ [MReg RSP])
                             -- :-O  should add Caller-saved registers
                where x = map MReg (catMaybes $ take nargs argOrder)
        Ret p rets -> (if rets then [MReg RAX] else [], []) <+> (map MReg A.calleeSaved ++ [MReg RSP], [])
        RetPop p rets num -> (if rets then [MReg RAX] else [], []) <+> (map MReg A.calleeSaved ++ [MReg RSP], [])
        ExitFail{} -> emptyAD
--        Realign{} -> ([MReg RSP], [MReg RSP])
--        Unrealign{} -> ([MReg RSP], [MReg RSP])
        Lea p m r -> getRSrc m <+> getRDst r
        Push p irm -> getRSrc irm <+> ([MReg RSP], [MReg RSP])
        Pop p rm -> getRDst rm <+> ([MReg RSP], [MReg RSP])
        Jmp{} -> emptyAD
        JCond{} -> emptyAD
        ALU_IRMtoR _ _ irm r -> getRSrc irm <+> getRSrc r <+> getRDst r
        ALU_IRtoM _ _ ir m -> getRSrc ir <+> getRSrc m <+> getRDst m
        Cmp _ ir rm -> getRSrc ir <+> getRSrc rm
        Test _ ir rm -> getRSrc ir <+> getRSrc rm
        Inc _ rm -> getRSrc rm <+> getRDst rm
        Dec _ rm -> getRSrc rm <+> getRDst rm
        Neg _ rm -> getRSrc rm <+> getRDst rm
        IMulRAX _ rm -> getRSrc rm <+> ([MReg RAX], [MReg RAX, MReg RDX])
        IMulRM _ rm r -> getRSrc rm <+> getRSrc r <+> getRDst r
        IMulImm _ i rm r -> getRSrc rm <+> getRDst r
        IDiv _ rm -> getRSrc rm <+> ([MReg RDX, MReg RAX], [MReg RAX, MReg RDX])
        Cqo _ -> ([MReg RAX], [MReg RDX])
        Shl _ _ rm -> getRSrc rm <+> getRDst rm
        Shr _ _ rm -> getRSrc rm <+> getRDst rm
        Sar _ _ rm -> getRSrc rm <+> getRDst rm
        Nop _ -> emptyAD

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