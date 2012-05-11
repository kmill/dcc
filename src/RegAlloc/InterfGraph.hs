{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

module RegAlloc.InterfGraph where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.List
import Data.Maybe
import Data.Function
import Control.Monad
import DataflowTypes
import AST(noPosition, SourcePos)
import qualified IR as I
import Assembly
import AliveDead
import Compiler.Hoopl
import Util.NodeLocate

---
--- Webs
---
      
data DU = DU { duReg :: Reg
             , duSpilled :: Bool
             , duMoveNodes :: S.Set MovePtr
             , duPrecolored :: Bool
             , duDef :: NodePtr
             , duExtent :: S.Set NodePtr
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
               , webExtent :: S.Set NodePtr
               , webUses :: S.Set NodePtr }
         deriving (Show, Eq, Ord)

-- | A short web is one which shouldn't be spilled because it's just so short.
isShortWeb :: Web -> Bool
isShortWeb w = S.null $ webExtent w

wUnion :: Web -> Web -> Web
wUnion (Web r1 sr1 mr1 pc1 dus1 ds1 ex1 us1)
       (Web r2 sr2 mr2 pc2 dus2 ds2 ex2 us2)
  = Web 
    { webReg = r1 
    , webSpilled = sr1 || sr2
    , webMoveNodes = mr1 `S.union` mr2
    , webPrecolored = pc1 || pc2
    , webDUs = dus1 `S.union` dus2
    , webDefs = ds1 `S.union` ds2 
    , webExtent = ex1 `S.union` ex2 
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
    , igRRMoves :: MoveFact
    , igFixedRegs :: M.Map Reg (S.Set WebID)
    }
                   deriving Show

type InterfGraphs = M.Map Label InterfGraph

-- | Adds an edge (commutitatively) to the interference graph.
addInterfEdge :: WebID -> WebID -> InterfGraph -> InterfGraph
addInterfEdge u v g = g { igAdjLists = add u v $ add v u $ igAdjLists g }
    where add a b adj = M.adjust (S.insert b) a adj

-- | Checks whether two webs interfere
wInterf :: Web -> Web -> Bool
wInterf (Web r1 _ _ _ dus1 ds1 ex1 us1) (Web r2 _ _ _ dus2 ds2 ex2 us2)
    = if notUsable r1 || notUsable r2 -- basically, we don't want RSP to interfere
      then False
      else (S.union ds1 ex1 `ints` S.union ds2 ex2)
               || (S.union ex1 us1 `ints` S.union ex2 us2)
      where ints s1 s2 = not $ S.null $ S.intersection s1 s2
            notUsable (MReg r) = r `notElem` usableRegisters
            notUsable (SReg _) = False


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

-- | (dus, tomatch, extents)
type DUBuildFact = (S.Set DU, S.Set (Reg, Bool, NodePtr, S.Set MovePtr), S.Set (Reg, NodePtr))

duLattice :: DataflowLattice DUBuildFact
duLattice = DataflowLattice
            { fact_name = "du lattice"
            , fact_bot = (S.empty, S.empty, S.empty)
            , fact_join = add }
    where add :: JoinFun DUBuildFact
          add _ (OldFact (oldDUs, oldUndefs, oldExtents)) (NewFact (newDUs, newUndefs, newExtents))
              = (ch, (dus', undefs', extents'))
              where dus' = S.union oldDUs newDUs
                    undefs' = S.union oldUndefs newUndefs
                    extents' = S.union oldExtents newExtents
                    bigger :: forall a. S.Set a -> S.Set a -> Bool
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
          
          handle :: NodePtr
                 -> Bool -- ^ whether it's "spill-related"
                 -> S.Set NodePtr -- ^ the set of associated moves
                 -> AliveDead -- ^ the alive/dead (i.e., uses/defs) for the node
                 -> [Reg] -- ^ the pinned registers for the node
                 -> ([Reg], [Reg]) -- ^ the fixed uses/defs for the node
                 -> DUBuildFact
                 -> DUBuildFact
          handle l sr mr (uses, defs) pinned (fixedUses, fixedDefs) (dus, tomatch, extents)
              = let withdef d = S.map makeDU rps
                        where rps = S.filter (\(reg, fixed, ptr, moves) -> reg == d) tomatch
                              makeDU (reg, fixed, ptr, moves)
                                  = DU reg sr (mr `S.union` moves) (fixed || reg `elem` fixedDefs) l (ptrs reg) ptr
                    -- takes the NodePtrs from the current extents for a given register
                    ptrs r = S.map snd $ S.filter (\(reg, ptr) -> reg == r) extents
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
                    dduPinned = S.fromList $ map (\reg -> DU reg False mr False l S.empty l) pinned
                    alive = S.map fst extents
                    -- we clear the extents list of things which have been defined
                    extents' = S.filter (\(reg, ptr) -> reg `notElem` defs) extents
                    -- and extend the list for those which are still there
                    dextents = S.map (\(reg, fixed, ptr, moves) -> (reg, l)) tomatch'
                               `S.union` (S.fromList $ map (\reg -> (reg, l)) pinned)
                in ( S.unions [dus, ddu, dduPinned, ddvirtused]
                   , S.unions [tomatch', dtomatch]
                   , S.unions [extents', dextents] )

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
          
          duToWeb :: DU -> Web
          duToWeb du@(DU r sr mr fixed d ex u)
              = Web r sr mr (r == MReg RSP || fixed)
                (S.singleton du) (S.singleton d) ex (S.singleton u)
          duToWeb du@(DUv r sr fixed d)
              = Web r sr S.empty (r == MReg RSP || fixed) 
                (S.singleton du) (S.singleton d) S.empty S.empty
          
          -- | Checks whether two webs should be coalesced because
          -- they have the same register and because they either share
          -- a definition or use.  If they are precolored webs, then
          -- they can be coalesced by the fact they have the same
          -- register.
          wToCoalesce :: Web -> Web -> Bool
          wToCoalesce (Web r1 sr1 mr1 pc1 dus1 ds1 ex1 us1)
                      (Web r2 sr2 mr2 pc2 dus2 ds2 ex2 us2)
              = r1 == r2 && ((pc1 && pc2)
                             || not (S.null $ ds1 `S.intersection` ds2)
                             || not (S.null $ us1 `S.intersection` us2))
          
          
          iteration'' :: Web -> [Web] -> Maybe [Web]
          iteration'' w webs
              = let (int, nint) = partition (wToCoalesce w) webs
                in case length int of
                     1 -> Nothing
                     _ -> Just $ (foldl1 wUnion int):nint
          
          -- | Not really efficient... Iteratively coalesces webs
          -- which wToCoalesce says can be coalesced.
          iteration' :: [Web] -> [Web] -> [Web]
          iteration' [] webs = webs
          iteration' (w:tocheck) webs
              = case iteration'' w webs of
                  Nothing -> iteration' tocheck webs
                  Just webs' -> iteration' webs' webs'

-- | Builds the interference graph for all the webs by running wInterf
-- on all pairs of webs.
makeInterfGraph :: [Web] -> MoveFact -> InterfGraph
makeInterfGraph webs rrmoves = InterfGraph idToWebMap mkAdjs rrmoves fixedRegs
    where idToWeb = zip [0..] webs
          idToWebMap = M.fromList idToWeb
          mkAdj i w = S.fromList $ do
                        (j, w') <- idToWeb
                        guard $ i /= j
                        guard $ wInterf w w'
                        return j
          mkAdjs = M.fromList $ do
                     (i, w) <- idToWeb
                     return (i, mkAdj i w)
          fixedRegs = M.mapKeysWith S.union webReg $
                      M.fromList $ do (i, w) <- idToWeb
                                      return (w, S.singleton i)

-- | Finds all register-to-register moves in the graph.
getRegRegMoves :: [Label] -> Graph (PNode Asm) C C -> M.Map Label MoveFact
getRegRegMoves mlabels graph
    = M.fromList $ map (\l -> (l, fromJust $ lookupFact l facts)) mlabels
    where rrLattice :: DataflowLattice MoveFact
          rrLattice = DataflowLattice
                      { fact_name = "rrLatice"
                      , fact_bot = S.empty
                      , fact_join = add }
              where add _ (OldFact s1) (NewFact s2) = (ch, s')
                        where s' = S.union s1 s2
                              ch = changeIf $ S.size s' > S.size s1
          rrTransfer :: BwdTransfer (PNode Asm) MoveFact
          rrTransfer = mkBTransfer3 fe fm fx
              where fe :: PNode Asm C O -> MoveFact -> MoveFact
                    fe _ f = f
                    fm :: PNode Asm O O -> MoveFact -> MoveFact
                    fm (PNode l (MovIRMtoR _ (IRM_R sreg) dreg)) f
                        = S.insert (l, sreg, dreg) f
                    fm _ f = f
                    fx :: PNode Asm O C -> FactBase MoveFact -> MoveFact
                    fx n fs = joinOutFacts rrLattice n fs
          rrPass :: Monad m => BwdPass m (PNode Asm) MoveFact
          rrPass = BwdPass
                   { bp_lattice = rrLattice
                   , bp_transfer = rrTransfer
                   , bp_rewrite = noBwdRewrite }
          doRR :: RM (FactBase MoveFact)
          doRR = do (_, f, _) <- analyzeAndRewriteBwd
                                 rrPass
                                 (JustC mlabels)
                                 graph
                                 mapEmpty
                    return f
          facts :: FactBase MoveFact
          facts = I.runGM $ evalStupidFuelMonad doRR 2222222

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
