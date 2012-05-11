{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

module AliveDead where

---
--- Aliveness/deadness (aka use/definition)
---

import Assembly
import Data.Maybe


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

-- | Gets the registers which are used and defined (also known as
-- "alive" and "dead", respectively, because of backwards liveness
-- analysis).
getAliveDead :: forall e x. Asm e x -> AliveDead
getAliveDead expr
    = case expr of
        Label{} -> emptyAD
        Spill _ r d -> getRSrc r <+> ([MReg RSP], [])
        Reload _ s r -> getRDst r <+> ([MReg RSP], [])
        MovIRMtoR _ irm r -> getRSrc irm <+> getRDst r
        MovIRtoM _ ir m -> getRSrc ir <+> getRDst m
        Mov64toR _ i r -> getRDst r
        CMovRMtoR _ _ rm r -> getRSrc rm <+> getRSrc r <+> getRDst r
        Enter _ _ nargs _ -> ([], x) <+> ([], map MReg calleeSaved ++ [MReg RSP])
                where x = map MReg (catMaybes $ take nargs argOrder)
        Leave _ rets _ -> (map MReg calleeSaved ++ [MReg RSP], []) <+> (if rets then [MReg RAX] else [], [])
        Call p nargs fl -> (x, x ++ [MReg RAX])
                           <+> ([MReg RSP], map MReg callerSaved ++ [MReg RSP])
                where x = map MReg (catMaybes $ take nargs argOrder)
        Callout p nargs fl -> (x ++ [MReg RAX], x ++ [MReg RAX])
                              <+> ([MReg RSP], map MReg callerSaved ++ [MReg RSP])
                where x = map MReg (catMaybes $ take nargs argOrder)
        Ret p rets -> (if rets then [MReg RAX] else [], []) <+> ([MReg RSP], [])
        RetPop p rets num -> (if rets then [MReg RAX] else [], []) <+> ([MReg RSP], [])
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