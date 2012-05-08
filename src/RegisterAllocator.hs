{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

module RegisterAllocator where 

import qualified Data.Map as Map 
import Assembly
import qualified Assembly as A
import CodeGenerate
import qualified IR as I
import Dataflow
import DataflowTypes
import qualified Data.Set as S
import Data.List
import Control.Monad.State
import Compiler.Hoopl
import Data.Maybe
import AST (SourcePos, noPosition)
import Debug.Trace

regAlloc :: LowIRRepr -> I.GM LowIRRepr
regAlloc (LowIRRepr fields strs meths graph)
    = do graph'' <- evalStupidFuelMonad (collectSpill mlabels graph') 22222222
         return $ LowIRRepr fields strs meths graph''
      where GMany _ body _ = graph
            graph' = foldl (|*><*|) emptyClosedGraph bodies
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
                g (Enter p l _) _ = fromMaybe S.empty (lookupFact l fb)
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
                d (A.Enter pos l x) f = if x' == x
                                        then return Nothing
                                        else return $ Just $ mkFirst $
                                             A.Enter pos l x'
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
mapRR f a@(Realign{}) = a
mapRR f a@(Unrealign{}) = a
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
        Enter _ _ i -> (x, x)
                where x = map MReg (catMaybes $ take i argOrder)
        Leave{} -> emptyAD
        Call p nargs i -> (x, [MReg RAX])
                where x = map MReg (catMaybes $ take nargs argOrder)
        Callout p nargs i -> (x ++ [MReg RAX], [MReg RAX])
                             -- :-O  should add Caller-saved registers
                where x = map MReg (catMaybes $ take nargs argOrder)
        Ret p rets -> (if rets then [MReg RAX] else [], [])
        RetPop p rets num -> (if rets then [MReg RAX] else [], [])
        ExitFail{} -> emptyAD
        Realign{} -> emptyAD
        Unrealign{} -> emptyAD
        Lea p m r -> getRSrc m <+> getRDst r
        Push p irm -> getRSrc irm
        Pop p rm -> getRDst rm
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

