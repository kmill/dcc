{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

module RegAlloc.SimpleRegAlloc where 

import qualified Data.Map as Map 
import Assembly
import qualified Assembly as A
import CodeGenerate
import qualified IR as I
import Dataflow
import DataflowTypes
import Dataflow.DeadCodeAsm
import qualified Data.Set as S
import Data.List
import Control.Monad.State
import Compiler.Hoopl
import Data.Maybe
import AST (SourcePos, noPosition)
import Debug.Trace
import qualified RegAlloc.Allocator as Allocator
import AliveDead

regAlloc :: LowIRRepr -> I.GM LowIRRepr
regAlloc (LowIRRepr fields strs ipc meths graph)
    = return $ LowIRRepr fields strs ipc meths graph'
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
      mkReload, mkSpill :: String -> Graph Asm O O
      mkReload s = mkMiddle $ Reload noPosition (SpillSID s) (getMReg s)
      mkSpill s = mkMiddle $ Spill noPosition (getMReg s) (SpillSID s)
      reloads = catGraphs $ map mkReload salive
      spills = catGraphs $ map mkSpill sdead


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
