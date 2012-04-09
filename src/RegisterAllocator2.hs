{-# LANGUAGE RankNTypes, GADTs #-}

module RegisterAllocator2 where 

import qualified Data.Map as Map 
import Assembly2
import Control.Monad.State
import Compiler.Hoopl
import Data.Maybe
import AST (SourcePos)



type AliveDead = ([Reg], [Reg])
class GetRegs x where
    getRSrc :: x -> AliveDead
    getRDst :: x -> AliveDead

emptyAD :: AliveDead
emptyAD = ([], [])

infixl 5 @>

(@>) :: AliveDead -> AliveDead -> AliveDead
(a1,d1) @> (a2,d2) = (a1++a2, d1++d2)

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
mapRR f (Lea p m r) = Lea p (map_M f m) (f r)
mapRR f (Push p irm) = Push p (map_IRM f irm)
mapRR f (Pop p rm) = Pop p (map_RM f rm)
mapRR f a@(Jmp{}) = a
mapRR f a@(JCond{}) = a
mapRR f (ALU_IRMtoR p op irm r) = ALU_IRMtoR p op (map_IRM f irm) (f r)
mapRR f (ALU_IRtoM p op ir m) = ALU_IRtoM p op (map_IR f ir) (map_M f m)
mapRR f (Cmp p ir rm) = Cmp p (map_IR f ir) (map_RM f rm)
mapRR f (Inc p rm) = Inc p (map_RM f rm)
mapRR f (Dec p rm) = Dec p (map_RM f rm)
mapRR f (Neg p rm) = Neg p (map_RM f rm)
mapRR f (IMulRAX p rm) = IMulRAX p (map_RM f rm)
mapRR f (IMulRM p rm r) = IMulRM p (map_RM f rm) (f r)
mapRR f (IMulImm p i rm r) = IMulImm p i (map_RM f rm) (f r)
mapRR f (IDiv p rm) = IDiv p (map_RM f rm)
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
        MovIRMtoR _ irm r -> getRSrc irm @> getRDst r
        MovIRtoM _ ir m -> getRSrc ir @> getRDst m
        Mov64toR _ i r -> getRDst r
        CMovRMtoR _ _ rm r -> getRSrc rm @> getRSrc r @> getRDst r
        Enter _ _ i -> (x, x)
                where x = map MReg (catMaybes $ take i argOrder)
        Leave{} -> emptyAD
        Call p nargs i -> (x, [MReg RAX])
                where x = map MReg (catMaybes $ take nargs argOrder)
        Callout p nargs i -> (x, [MReg RAX])
                where x = map MReg (catMaybes $ take nargs argOrder)
        Ret p rets -> (if rets then [MReg RAX] else [], [])
        RetPop p rets num -> (if rets then [MReg RAX] else [], [])
        ExitFail{} -> emptyAD
        Lea p m r -> getRSrc m @> getRDst r
        Push p irm -> getRSrc irm
        Pop p rm -> getRDst rm
        Jmp{} -> emptyAD
        JCond{} -> emptyAD
        ALU_IRMtoR _ _ irm r -> getRSrc irm @> getRDst r
        ALU_IRtoM _ _ ir m -> getRSrc ir @> getRDst m
        Cmp _ ir rm -> getRSrc ir @> getRSrc rm
        Inc _ rm -> getRSrc rm @> getRDst rm
        Dec _ rm -> getRSrc rm @> getRDst rm
        Neg _ rm -> getRSrc rm @> getRDst rm
        IMulRAX _ rm -> getRSrc rm @> ([MReg RAX], [MReg RAX, MReg RDX])
        IMulRM _ rm r -> getRSrc rm @> getRSrc r @> getRDst r
        IMulImm _ i rm r -> getRSrc rm @> getRDst r
        IDiv _ rm -> getRSrc rm @> ([MReg RDX, MReg RAX], [MReg RAX, MReg RDX])
        Shl _ _ rm -> getRSrc rm @> getRDst rm
        Shr _ _ rm -> getRSrc rm @> getRDst rm
        Sar _ _ rm -> getRSrc rm @> getRDst rm
        Nop _ -> emptyAD

