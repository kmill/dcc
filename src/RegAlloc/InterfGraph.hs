{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

module RegAlloc.InterfGraph where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.List
import Data.Maybe
import Data.Function
import Control.Monad
import DataflowTypes
import Dataflow.OptSupport
import AST(noPosition, SourcePos)
import qualified IR as I
import Assembly
import AliveDead
import Compiler.Hoopl
import Util.NodeLocate
import Debug.Trace

---
--- Webs
---
      
data DU = DU { duReg :: Reg
             , duSpilled :: Bool
             , duMoveNodes :: S.Set MovePtr
             , duPrecolored :: Bool
             , duDef :: NodePtr
             , duUse :: NodePtr }
        | DUv { duReg :: Reg
              , duSpilled :: Bool
              , duPrecolored :: Bool
              , duDef :: NodePtr } -- ^ Represents a register which is
                                   -- defined but not used.  It should
                                   -- still be given a chance to
                                   -- interfere!
          deriving (Eq, Ord, Show)

data Web = Web { webReg :: Reg
               , webSpilled :: Bool
               , webMoveNodes :: S.Set MovePtr
               , webPrecolored :: Bool
               , webDUs :: S.Set DU
               , webDefs :: S.Set NodePtr
               , webUses :: S.Set NodePtr }
         deriving (Show, Eq, Ord)

wUnion :: Web -> Web -> Web
wUnion (Web r1 sr1 mr1 pc1 dus1 ds1 us1)
       (Web r2 sr2 mr2 pc2 dus2 ds2 us2)
  = Web 
    { webReg = r1 
    , webSpilled = sr1 || sr2
    , webMoveNodes = mr1 `S.union` mr2
    , webPrecolored = pc1 || pc2
    , webDUs = dus1 `S.union` dus2
    , webDefs = ds1 `S.union` ds2 
    , webUses = us1 `S.union` us2 }


---
--- Interference graphs
---

type WebID = Int
type MovePtr = NodePtr

-- | Represents the reg to reg moves
type MoveFact = S.Set (MovePtr, Reg, Reg)

data InterfGraph = InterfGraph
    { igIDToWeb :: M.Map WebID Web
    , igAdjLists :: M.Map WebID (S.Set WebID)
    , igRRMoves :: S.Set MovePtr
    , igFixedRegs :: M.Map Reg (S.Set WebID)
    }
                   deriving Show

type InterfGraphs = M.Map Label InterfGraph

-- | Adds an edge (commutitatively) to the interference graph.
addInterfEdge :: WebID -> WebID -> InterfGraph -> InterfGraph
addInterfEdge u v g = g { igAdjLists = add u v $ add v u $ igAdjLists g }
    where add a b adj = M.adjust (S.insert b) a adj


-- | Gets the degree of a web in the interference graph.
webDegree :: WebID -> InterfGraph -> Int
webDegree i g = S.size $ igAdjLists g M.! i

-- | Gets the list of web ids from an interference graph.
igWebIDs :: InterfGraph -> [WebID]
igWebIDs g = M.keys $ igIDToWeb g

-- | Gets the web by id from the interference graph.
igGetWeb :: WebID -> InterfGraph -> Web
igGetWeb i g = igIDToWeb g M.! i

---
--- Building the webs
---

-- | (dus, tomatch)
type DUBuildFact = (S.Set DU, S.Set (Reg, Bool, NodePtr, S.Set MovePtr))

duLattice :: DataflowLattice DUBuildFact
duLattice = DataflowLattice
            { fact_name = "du lattice"
            , fact_bot = (S.empty, S.empty)
            , fact_join = joinProd joinSets joinSets }

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
          
          handle :: NodePtr
                 -> Bool -- ^ whether it's "spill-related"
                 -> S.Set NodePtr -- ^ the set of associated moves
                 -> AliveDead -- ^ the alive/dead (i.e., uses/defs) for the node
                 -> [Reg] -- ^ the pinned registers for the node
                 -> ([Reg], [Reg]) -- ^ the fixed uses/defs for the node
                 -> DUBuildFact
                 -> DUBuildFact
          handle l sr mr (uses, defs) pinned (fixedUses, fixedDefs) (dus, tomatch)
              = let withdef d = S.map makeDU rps
                        where rps = S.filter (\(reg, fixed, ptr, moves) -> reg == d) tomatch
                              makeDU (reg, fixed, ptr, moves)
                                  = DU reg sr (mr `S.union` moves) (fixed || reg `elem` fixedDefs) l ptr
                    -- we can remove things which have been defined
                    tomatch' = S.filter (\(reg, fixed, ptr, moves) -> reg `notElem` defs) tomatch
                    -- we want to add the used things to the tomatch list
                    dtomatch = S.fromList $ map (\r -> (r, r `elem` fixedUses, l, mr)) uses
                    -- we add entries for things which are defined but
                    -- not used so caller-saved registers work
                    ddvirtused = S.fromList [DUv reg sr (reg `elem` fixedDefs) l
                                            | reg <- defs, reg `S.notMember` matchregs]
                    matchregs = S.map (\(reg, fixed, ptr, moves) -> reg) tomatch
                    -- these are the matched definitions to put in the
                    -- dus set
                    ddu = S.unions $ map withdef defs
                    -- some variables are "pinned" across use/def boundaries
                    dduPinned = S.fromList $ map (\reg -> DU reg False mr False l l) pinned
                in ( S.unions [dus, ddu, dduPinned, ddvirtused]
                   , S.unions [tomatch', dtomatch] )

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
            getDUs (a, b) = a

collectWebs :: S.Set DU -> [Web]
collectWebs dus = iteration (M.keys webmap) webmap M.empty M.empty M.empty M.empty
    where webs = map duToWeb (S.toList dus)
          webmap = M.fromList $ zip [0..] webs
          
          duToWeb :: DU -> Web
          duToWeb du@(DU r sr mr fixed d u)
              = Web r sr mr (r == MReg RSP || fixed)
                (S.singleton du) (S.singleton d) (S.singleton u)
          duToWeb du@(DUv r sr fixed d)
              = Web r sr S.empty (r == MReg RSP || fixed) 
                (S.singleton du) (S.singleton d) S.empty
          
          getAlias :: WebID -> M.Map WebID WebID -> WebID
          getAlias i aliases = case M.lookup i aliases of
                                 Nothing -> i
                                 Just j -> getAlias j aliases
          insertAlias :: WebID -> WebID -> M.Map WebID WebID -> M.Map WebID WebID
          insertAlias i j aliases | i == j = aliases
                                  | otherwise = M.insert i j aliases
          
          iteration :: [WebID] -- ^ webs to check
                       -> M.Map WebID Web -- ^ all webs
                       -> M.Map Reg WebID -- ^ precolored webs
                       -> M.Map (Reg, NodePtr) WebID -- ^ definitions
                       -> M.Map (Reg, NodePtr) WebID -- ^ uses
                       -> M.Map WebID WebID -- ^ aliases
                       -> [Web]
          iteration tocheck webs pcwebs defs uses aliases
              = case tocheck of
                  [] -> coalesceAliases M.empty (M.keys webs)
                      where coalesceAliases :: M.Map WebID Web -> [WebID] -> [Web]
                            coalesceAliases currmap []
                                = M.elems currmap
                            coalesceAliases currmap (w:ws)
                                = let w' = getAlias w aliases
                                      currmap' = M.insertWith wUnion w' (webs M.! w) currmap
                                  in coalesceAliases currmap' ws
                  w:ws -> let (w', defs', aliases') = handle (S.toList $ webDefs web) w defs aliases
                              (w'', uses', aliases'') = handle (S.toList $ webUses web) w' uses aliases'
                              (pcwebs', aliases''')
                                  = case webPrecolored web of
                                      False -> (pcwebs, aliases'')
                                      True -> case M.lookup (webReg web) pcwebs of
                                                Nothing -> (M.insert (webReg web) w'' pcwebs, aliases'')
                                                Just pcw -> (pcwebs, insertAlias w'' (getAlias pcw aliases'') aliases'')
                                   
                              web = webs M.! w
                              
                              handle :: [NodePtr] -> WebID -> M.Map (Reg, NodePtr) WebID -> M.Map WebID WebID
                                     -> (WebID, M.Map (Reg, NodePtr) WebID, M.Map WebID WebID)
                              handle [] w checkmap aliasmap = (w, checkmap, aliasmap)
                              handle (n:ns) w checkmap aliasmap
                                  = case M.lookup (webReg web, n) checkmap of
                                      Just w' -> let w'' = getAlias w' aliasmap
                                                 in handle ns w'' checkmap (insertAlias w w'' aliasmap)
                                      Nothing -> handle ns w (M.insert (webReg web, n) w checkmap) aliasmap
                                      
                          in iteration ws webs pcwebs' defs' uses' aliases'''

-- | Builds the interference graph.
makeInterfGraph :: [Label] -> Graph (PNode Asm) C C -> [Web] -> InterfGraph
makeInterfGraph mlabels graph webs = InterfGraph idToWebMap adjs moves fixedRegs
    where idToWeb = zip [0..] webs
          idToWebMap = M.fromList idToWeb
          moves = S.unions $ map webMoveNodes webs
          fixedRegs = M.mapKeysWith S.union webReg $
                      M.fromList $ do (i, w) <- idToWeb
                                      return (w, S.singleton i)
          
          combineUsedef (a1, b1) (a2, b2) = (a1 `S.union` a2, b1 `S.union` b2)
          
          addUse w u usedef = M.insertWith combineUsedef u (S.singleton w, S.empty) usedef
          addDef w d usedef = M.insertWith combineUsedef d (S.empty, S.singleton w) usedef
          
          -- | A map from nodes to (alive, dead) sets of WebIDs
          usedef = foldl (flip id) M.empty ([addDef w d | (w, web) <- idToWeb, d <- S.toList $ webDefs web]
                                            ++ [addUse w u | (w, web) <- idToWeb, u <- S.toList $ webUses web])
          
          -- | The adjacency lists!
          adjs = let adjm = buildAdjLists mlabels graph usedef
                 in M.unions [adjm M.! l | l <- mlabels]

type AdjListFact = (S.Set WebID, M.Map WebID (S.Set WebID))

buildAdjLists :: [Label] -> Graph (PNode Asm) C C -> M.Map NodePtr (S.Set WebID, S.Set WebID)
              -> M.Map Label (M.Map WebID (S.Set WebID))
buildAdjLists mlabels graph usedef
    = M.fromList $ map (\l -> (l, snd $ fromJust $ lookupFact l facts)) mlabels
    where alLattice :: DataflowLattice AdjListFact
          alLattice = DataflowLattice
                      { fact_name = "alLattice"
                      , fact_bot = (S.empty, M.empty)
                      , fact_join = add }
              where add _ (OldFact (live1, adj1)) (NewFact (live2, adj2)) = (ch, (live', adj'))
                        where live' = S.union live1 live2
                              ch = changeIf $ S.size live' > S.size live1 || adjch
                              (adjch, adj') = M.foldrWithKey madd (False, adj1) adj2
                              madd k new_v (mch, joinmap) =
                                  case M.lookup k joinmap of
                                    Nothing -> (True, M.insert k new_v joinmap)
                                    Just old_v -> let v' = S.union old_v new_v
                                                      mch' = S.size v' > S.size old_v
                                                  in if mch'
                                                     then (True, M.insert k v' joinmap)
                                                     else (mch, joinmap)
          alTransfer :: BwdTransfer (PNode Asm) AdjListFact
          alTransfer = mkBTransfer3 fe fm fx
              where fe :: PNode Asm C O -> AdjListFact -> AdjListFact
                    fe (PNode l n) f = handle (M.findWithDefault (S.empty, S.empty) l usedef) f
                    fm :: PNode Asm O O -> AdjListFact -> AdjListFact
                    fm (PNode l (MovIRMtoR _ (IRM_R _) _)) (live, adj)
                        = let (alive, dead) = usedef M.! l
                          in handle (alive, dead) (live S.\\ alive, adj)
                    fm (PNode l n) f = handle (M.findWithDefault (S.empty, S.empty) l usedef) f
                    fx :: PNode Asm O C -> FactBase AdjListFact -> AdjListFact
                    fx (PNode l n) fs = handle (M.findWithDefault (S.empty, S.empty) l usedef) (joinOutFacts alLattice n fs)
                    
                    handle :: (S.Set WebID, S.Set WebID) -> AdjListFact -> AdjListFact
                    handle (alive, dead) (live, adj)
                        = let live' = live S.\\ dead
                              addEdge u v adjlist | u == v = adjlist
                                                  | otherwise = add u v $ add v u adjlist
                                                  where add u v al = M.insertWith S.union u (S.singleton v) al
                              adj' = foldl (flip id) adj [addEdge d l | d <- S.toList dead, l <- S.toList live]
                          in (alive `S.union` (live' S.\\ dead), adj')
          alPass :: Monad m => BwdPass m (PNode Asm) AdjListFact
          alPass = BwdPass
                   { bp_lattice = alLattice
                   , bp_transfer = alTransfer
                   , bp_rewrite = noBwdRewrite }
          doAL :: RM (FactBase AdjListFact)
          doAL = do (_, f, _) <- analyzeAndRewriteBwd
                                 alPass
                                 (JustC mlabels)
                                 graph
                                 mapEmpty
                    return f
          facts :: FactBase AdjListFact
          facts = I.runGM $ evalStupidFuelMonad doAL 2222222

-- | Inserts moves for each fixed register so that we can properly
-- spill them.  This is run before register allocation itself.  Only
-- fixed registers which are alive have moves inserted.
massageGraph :: [Label] -> Graph Asm C C -> RM (Graph Asm C C)
massageGraph mlabels graph
    = do (g, _ ,_) <- analyzeAndRewriteBwd
                      massageGraphPass
                      (JustC mlabels)
                      graph
                      (mapFromList (map (\l -> (l, S.empty)) mlabels))
         return g
    where
      massageGraphPass :: FuelMonad m => BwdPass m Asm (S.Set Reg)
      massageGraphPass = BwdPass
                         { bp_lattice = liveLattice
                         , bp_transfer = liveTransfer
                         , bp_rewrite = mkBRewrite3 mCO mOO mOC }
      liveLattice :: DataflowLattice (S.Set Reg)
      liveLattice = DataflowLattice
                    { fact_name = "liveness"
                    , fact_bot = S.empty
                    , fact_join = add }
        where add _ (OldFact old) (NewFact new) = (ch, j)
                where j = new `S.union` old
                      ch = changeIf (S.size j > S.size old) 
      liveTransfer :: BwdTransfer Asm (S.Set Reg)
      liveTransfer = mkBTransfer3 g g' g''
          where 
            g e f = handle (getAliveDead e) f
            g' e f = handle (getAliveDead e) f
            g'' e f = handle (getAliveDead e) (joinOutFacts liveLattice e f)
            
            handle :: ([Reg], [Reg]) -> S.Set Reg -> S.Set Reg
            handle (alive, dead) f = (f S.\\ (S.fromList dead)) `S.union` (S.fromList alive)
      
      mkMove :: SourcePos -> Reg -> Asm O O 
      mkMove pos r = MovIRMtoR pos (IRM_R r) r
      mkMoves :: SourcePos -> [Reg] -> Graph Asm O O 
      mkMoves pos regs = mkMiddles [mkMove pos r | r <- nub regs, r /= MReg RSP]
      ifNotNull :: forall a b m. (Monad m) => [a] -> b -> m (Maybe b)
      ifNotNull l x = return $ if null l then Nothing else Just x
      
      aliveDefined defined f = S.toList $ S.fromList defined `S.intersection` f
      
      mCO :: Monad m => Asm C O -> S.Set Reg ->  m (Maybe (Graph Asm C O))
      mCO n f = ifNotNull defined' $ mkFirst n <*> mkMoves pos defined'
          where (used, defined) = getFixed n
                defined' = aliveDefined defined f
                pos = noPosition
      mOO :: Monad m => Asm O O -> S.Set Reg -> m (Maybe (Graph Asm O O))
      mOO n f = ifNotNull (used ++ defined') $
                mkMoves pos used <*> mkMiddle n <*> mkMoves pos defined'
          where (used, defined) = getFixed n
                defined' = aliveDefined defined f
                pos = noPosition
      mOC :: Monad m => Asm O C -> FactBase (S.Set Reg) -> m (Maybe (Graph Asm O C))
      mOC n f = ifNotNull used $ mkMoves pos used <*> mkLast n
          where (used, defined) = getFixed n
                pos = noPosition


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
        Enter _ _ i _ -> []
        Leave{} -> [MReg RSP]
        Call p nargs i -> [MReg RSP]
        Callout p nargs i -> [MReg RSP]
        Ret p rets -> []
        RetPop p rets num -> []
        ExitFail{} -> []
--        Realign{} -> []
--        Unrealign{} -> []
        Lea p m r -> []
        Push p irm -> [MReg RSP]
        Pop p rm -> [MReg RSP]
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
        Spill _ r d -> ([MReg RSP], [])
        Reload _ s r -> ([MReg RSP], [])
        MovIRMtoR _ irm r -> noFixed
        MovIRtoM _ ir m -> noFixed
        Mov64toR _ i r -> noFixed
        CMovRMtoR _ _ rm r -> noFixed
        Enter _ _ nargs _ -> ([], x ++ map MReg calleeSaved ++ [MReg RSP]) 
            where x = map MReg (catMaybes $ take nargs argOrder)
        Leave _ rets _ -> (if rets then [MReg RAX] else [], [])
                          <+> ([MReg RSP] ++ map MReg calleeSaved, [MReg RSP])
        Call p nargs i -> (x, reverse x ++ [MReg RAX])
                          <+> ([MReg RSP], map MReg callerSaved ++ [MReg RSP])
            where x = map MReg (catMaybes $ take nargs argOrder)
        Callout p nargs i -> ([MReg RAX] ++ x, x ++ [MReg RAX])
                             <+> ([MReg RSP], map MReg callerSaved ++ [MReg RSP])
            where x = map MReg (catMaybes $ take nargs argOrder)
        Ret p rets -> (if rets then [MReg RAX] else [], []) <+> ([MReg RSP], [])
        RetPop p rets num -> (if rets then [MReg RAX] else [], []) <+> ([MReg RSP], [])
        ExitFail{} -> noFixed
--        Realign{} -> []
--        Unrealign{} -> []
        Lea p m r -> noFixed
        Push p irm -> ([MReg RSP], [MReg RSP])
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
      where noFixed :: ([Reg], [Reg])
            noFixed = ([], [])
