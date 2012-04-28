{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

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
    = do graph'' <- evalStupidFuelMonad (collectSpill mlabels graph') 22222222
         return $ LowIRRepr fields strs meths graph''
      where GMany _ body _ = graph
            pg = toPGraph graph
            dus = collectDU mlabels pg
            webs = M.map (outputWebGraph . makeInterfGraph . collectWebs) dus
            graph' = coalesceRegisters mlabels pg --intercalate "\n" $ map snd (M.toList webs)
--            graph' = foldl (|*><*|) emptyClosedGraph bodies
            bodies = map f (mapElems body)
            f :: Block Asm C C -> Graph Asm C C
            f block = mkFirst e
                      <*> catGraphs (map withSpills inner)
                      <*> mkLast x
                where (me, inner, mx) = blockToNodeList block
                      e :: Asm C O
                      x :: Asm O C
                      e = case me of
                            JustC e' -> e'
                      x = case mx of
                            JustC x' -> x'
            mlabels = map I.methodEntry meths

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



collectSpillPass :: (CheckpointMonad m, FuelMonad m)
                    => BwdPass m A.Asm (S.Set String)
collectSpillPass = BwdPass
                   { bp_lattice = getSpillLattice
                   , bp_transfer = getSpillTransfer
                   , bp_rewrite = noBwdRewrite }
    where
      getSpillLattice :: DataflowLattice (S.Set String)
      getSpillLattice = DataflowLattice
                        { fact_name = "spill lattice"
                        , fact_bot = S.empty
                        , fact_join = add
                        }
          where add _ (OldFact old) (NewFact new) = (ch, j)
                    where j = S.union new old
                          ch = changeIf $ S.size j > S.size old

      getSpillTransfer :: BwdTransfer A.Asm (S.Set String)
      getSpillTransfer = mkBTransfer3 usedCO usedOO usedOC
          where
            usedCO :: A.Asm C O -> (S.Set String) -> (S.Set String)
            usedCO _ f = f

            usedOO :: A.Asm O O -> (S.Set String) -> (S.Set String)
            usedOO (A.Spill _ _ s) f = S.insert s f
            usedOO (A.Reload _ s _) f = S.insert s f
            usedOO _ f = f

            usedOC :: A.Asm O C -> FactBase (S.Set String) -> (S.Set String)
            usedOC x f = S.unions $ map
                         ((fromMaybe S.empty) . (flip lookupFact f))
                         (successors x)

rewriteSpillPass :: (CheckpointMonad m, FuelMonad m) =>
                    FactBase (S.Set String) -> FwdPass m Asm (S.Set String)
rewriteSpillPass fb = FwdPass 
                      { fp_lattice = noLattice
                      , fp_transfer = sTransfer
                      , fp_rewrite = rewriteSpill }
    where noLattice :: DataflowLattice (S.Set String)
          noLattice = DataflowLattice
                      { fact_name = "simple replicate"
                      , fact_bot = S.empty
                      , fact_join = add }
              where add _ (OldFact old) (NewFact new) = (ch, j)
                        where j = S.union new old
                              ch = changeIf $ S.size j > S.size old
          sTransfer :: FwdTransfer Asm (S.Set String)
          sTransfer = mkFTransfer3 g g' g''
              where 
                g :: Asm C O -> S.Set String -> S.Set String
                g (Enter p l _ _) _ = fromMaybe S.empty (lookupFact l fb)
                g e f = f
                g' e f = f
                g'' e f = mkFactBase noLattice $ zip (successors e) (repeat f)

          rewriteSpill :: forall m. FuelMonad m => FwdRewrite m Asm (S.Set String)
          rewriteSpill = mkFRewrite d
              where 
                d :: Asm e x -> S.Set String -> m (Maybe (Graph Asm e x))
                d (A.Spill pos reg s) f
                    = return $ Just $ mkMiddle $ A.mov pos reg mem
                      where offset = negate (8 + 8 * (fromJust $ elemIndex s f'))
                            f' = S.toAscList (S.insert s f)
                            mem = A.MemAddr (Just $ A.MReg A.RBP)
                                  (A.Imm32 $ fromIntegral offset)
                                  Nothing A.SOne
                d (A.Reload pos s reg) f
                    = return $ Just $ mkMiddle $ A.mov pos mem reg
                      where offset = negate (8 + 8 * (fromJust $ elemIndex s f'))
                            f' = S.toAscList (S.insert s f)
                            mem = A.MemAddr (Just $ A.MReg A.RBP)
                                  (A.Imm32 $ fromIntegral offset)
                                  Nothing A.SOne
                d (A.Enter pos l n x) f = if x' == x
                                          then return Nothing
                                          else return $ Just $ mkFirst $
                                               A.Enter pos l n x'
                    where x' = fromIntegral $ 8 * (S.size f) + 8
                d _ f = return Nothing



freeRegs :: [Reg]
freeRegs = map MReg [R10, R11, R12, R13, R14, R15] -- put this in optimal order!

getSRegs :: [Reg] -> [String]
getSRegs [] = []
getSRegs ((SReg s):xs) = s:(getSRegs xs)
getSRegs (_:xs) = getSRegs xs

withSpills :: Asm O O -> Graph Asm O O
withSpills expr = reloads <*> expr' <*> spills
    where
      (alive, dead) = getAliveDead expr
      salive = getSRegs alive
      sdead = getSRegs dead
      sToRegs = zip (salive ++ sdead) freeRegs
      f :: Reg -> Reg
      f (SReg s) = getMReg s
      f r = r
      getMReg s = fromJust $ lookup s sToRegs
      expr' = mkMiddle $ mapRR f expr
      mkReload s = mkMiddle $ Reload noPosition s (getMReg s)
      mkSpill s = mkMiddle $ Spill noPosition (getMReg s) s
      reloads = catGraphs $ map mkReload salive
      spills = catGraphs $ map mkSpill sdead

---
--- Webs
---
      
data DU = DU { duReg :: Reg
             , duDef :: NodePtr
             , duExtent :: S.Set NodePtr
             , duUse :: NodePtr }
        | DUv { duReg :: Reg
              , duDef :: NodePtr } -- ^ Represents a register which is
                                   -- defined but not used.  It should
                                   -- still be given a chance to
                                   -- interfere!
          deriving (Eq, Ord, Show)
data Web = Web { webReg :: Reg
               , webDefs :: S.Set NodePtr
               , webExtent :: S.Set NodePtr
               , webUses :: S.Set NodePtr }
         deriving Show

-- | Checks whether two webs interfere
wInterf :: Web -> Web -> Bool
wInterf (Web _ ds1 ex1 us1) (Web _ ds2 ex2 us2)
    = (S.union ds1 ex1 `ints` S.union ds2 ex2)
      || (S.union ex1 us1 `ints` S.union ex2 us2)
      where ints s1 s2 = not $ S.null $ s1 `S.intersection` s2

type DUBuildFact = (S.Set DU, S.Set (Reg, NodePtr), S.Set (Reg, NodePtr))

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
          fe (PNode l n) f = handle l (getAliveDead n) (getPinned n) f
          fm :: (PNode Asm) O O -> DUBuildFact -> DUBuildFact
          fm (PNode l n) f = handle l (getAliveDead n) (getPinned n) f
          fx :: (PNode Asm) O C -> FactBase DUBuildFact -> DUBuildFact
          fx (PNode l n) fb = handle l (getAliveDead n) (getPinned n)
                              (joinOutFacts duLattice n fb)
          
          handle :: NodePtr -> AliveDead -> [Reg] -> DUBuildFact -> DUBuildFact
          handle l (uses, defs) pinned (dus, tomatch, extents)
              = let withdef d = let rps = S.filter (\(reg, ptr) -> reg == d) tomatch
                                in S.map (\(reg, ptr) -> DU reg l (ptrs reg) ptr) rps
                    ptrs r = S.map snd $ S.filter (\(reg, ptr) -> reg == r) extents
                    -- we can remove things which have been defined
                    tomatch' = S.filter (\(reg, ptr) -> reg `notElem` defs) tomatch
                    -- we want to add the used things to the tomatch list
                    dtomatch = S.fromList $ map (\r -> (r, l)) uses
                    -- we add entries for things which are defined but
                    -- not used so caller-saved registers work
                    ddvirtused = S.fromList [DUv reg l | reg <- defs, reg `S.notMember` matchregs]
                    matchregs = S.map (\(reg, ptr) -> reg) tomatch
                    -- these are the matched definitions to put in the
                    -- dus set
                    ddu = S.unions $ map withdef defs
                    -- some variables are "pinned" across use/def boundaries
                    dduPinned = S.fromList $ map (\reg -> DU reg l S.empty l) pinned
                    alive = S.map fst extents
                    -- we clear the extents list of things which have been defined
                    extents' = S.filter (\(reg, ptr) -> reg `notElem` defs) extents
                    -- and extend the list for those which are still there
                    dextents = S.map (\(reg, ptr) -> (reg, l)) tomatch'
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
          duToWeb (DU r d ex u) = Web r (S.singleton d) ex (S.singleton u)
          duToWeb (DUv r d) = Web r (S.singleton d) S.empty S.empty
          wToCoalesce (Web r1 ds1 ex1 us1) (Web r2 ds2 ex2 us2)
              = r1 == r2 && (not (S.null $ ds1 `S.intersection` ds2)
                             || not (S.null $ us1 `S.intersection` us2))
          wUnion (Web r1 ds1 ex1 us1) (Web r2 ds2 ex2 us2)
              = Web r1 (ds1 `S.union` ds2) (ex1 `S.union` ex2) (us1 `S.union` us2)
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

makeInterfGraph :: [Web] -> ([(Int, Web)], M.Map Int (S.Set Int))
makeInterfGraph webs = (weblist, mkAdjs)
    where weblist = zip [0..] webs
          mkAdj i w = S.fromList $ do
                        (j, w') <- weblist
                        guard $ i /= j
                        guard $ wInterf w w'
                        return j
          mkAdjs = M.fromList $ do
                     (i, w) <- weblist
                     return (i, mkAdj i w)

type RRFact = S.Set (NodePtr, Reg, Reg)

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

--coalesceRegisters :: [Label] -> Graph (PNode Asm) C C -> Graph (PNode Asm) C C
coalesceRegisters mlabels graph
    = error $ show (map getCoalesced mlabels)
    where dus = collectDU mlabels graph
          websm = M.map (makeInterfGraph . collectWebs) dus
          rrmm = getRegRegMoves mlabels graph
          getCoalesced lab
              = let (webs, ig) = websm M.! lab
                    webD l r = head $ do 
                                 (i, web) <- webs
                                 guard $ webReg web == r
                                 guard $ l `S.member` webDefs web
                                 return (i, web)
                    webU l r = head $ do 
                                 (i, web) <- webs
                                 guard $ webReg web == r
                                 guard $ l `S.member` webUses web
                                 return (i, web)
                    rrm = rrmm M.! lab
                    canCoalesce :: (NodePtr, Reg, Reg) -> Bool
                    canCoalesce (l, sreg, dreg) = trace (show (l, sreg, dreg)) $ not interferes
                        where (di, _) = webD l dreg
                              (si, _) = webU l sreg
                              interferes = si `S.member` (ig M.! di)
--                              isSReg (SReg _) = True
--                              isSReg (MReg _) = False
                    rrmOK = S.filter canCoalesce rrm
                in rrmOK

outputWebGraph :: ([(Int, Web)], M.Map Int (S.Set Int)) -> String
outputWebGraph (webs, g)
    = "graph {\n"
      ++ "_webs_ [shape=record,label=\"{" ++ intercalate "|" (map showWeb webs) ++ "}\"];\n"
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
          showWeb (i, web) = "{" ++ intercalate "|" [show i, wr, wd, we, wu] ++ "}"
              where wr = show $ webReg web
                    wd = show $ webDefs web
                    we = show $ webExtent web
                    wu = show $ webUses web

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
        Callout p nargs i -> (x, [MReg RAX]) <+> ([MReg RSP], map MReg A.callerSaved ++ [MReg RSP])
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