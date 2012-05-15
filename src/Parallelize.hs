{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}
module Parallelize where 

import Compiler.Hoopl
import Data.Maybe
import LoopAnalysis
import IR
import DataflowTypes
import qualified Data.Set as S
import qualified Data.List as L

import Debug.Trace

type MidIRMap = LabelMap (Block MidIRInst C C)

t :: (Show a) => a -> a
t x = traceShow x x

compare' :: Loop -> Loop -> Ordering
compare' loop1 loop2 =
    case compareBodies of
        EQ -> compare loop1 loop2
        res -> res
    where compareBodies = compare (S.size $ loop_body loop1) (S.size $ loop_body loop2)

performParallelizePass :: MidIRRepr -> RM MidIRRepr
performParallelizePass midir = foldl (>>=) (return midir) $ map forLoop $ t $ L.sortBy compare' $ S.toList goodLoops
    where goodLoops = analyzeParallelizationPass midir

-- Need to do some things here:
-- 1. Change loop header to instance of Parallel
-- 2. Change counter increment block's predecessor's exit to a Return
-- 3. Excise counter increment block
forLoop :: Loop -> MidIRRepr -> RM MidIRRepr
forLoop loop midir = return $ midir { midIRGraph = graph' }
    where graph = midIRGraph midir
          GMany _ blockMap _ = graph
          blockMap' = parallelHeader (t loop) $ fixIncPred loop blockMap
          graph' = GMany NothingO blockMap' NothingO

parallelHeader :: Loop -> MidIRMap -> MidIRMap
parallelHeader loop blockMap = mapInsert headerLabel headerBlock' $ mapDelete headerLabel blockMap
    where headerLabel = loop_header loop
          headerBlock = fromMaybe (error "couldn't find loop header") $ mapLookup headerLabel blockMap
          headerBlock' = mapBlock processHeader headerBlock
          processHeader :: forall e x. MidIRInst e x -> MidIRInst e x
          processHeader (CondBranch pos (BinOp _ CmpGTE _ (Lit _ count)) endlbl looplbl)
              = Parallel pos looplbl (MV $ "idx_" ++ (show headerLabel)) count endlbl
          processHeader inst@(CondBranch _ expr _ _) = traceShow expr inst
          processHeader inst = inst

-- returns ONE loop predecessor. is UNCHECKED whether there are more.
loopPred :: Loop -> MidIRMap -> Label -> Label
loopPred loop blockMap lbl
    = head $ map fst $ filter (elem lbl . successors . snd) loopList
    where list = mapToList blockMap
          loopList = filter (\(l, b) -> S.member l $ loop_body loop) list

fixIncPred :: Loop -> MidIRMap -> MidIRMap
fixIncPred loop blockMap
    = mapInsert lastLabel lastBlock' $ mapDelete lastLabel $ mapDelete incLabel blockMap
    where incLabel = loopPred loop blockMap headerLabel
          lastLabel = loopPred loop blockMap incLabel
          lastBlock = fromMaybe (error "couldn't find last") $ mapLookup lastLabel blockMap
          lastBlock' = mapBlock processLast lastBlock
          processLast :: forall e x. MidIRInst e x -> MidIRInst e x
          processLast inst@(Branch pos lbl)
              | lbl == incLabel = ThreadReturn pos elbl
              | otherwise = error "Error in loop processing :-("
          processLast inst = inst
          headerLabel = loop_header loop
          headerBlock = fromMaybe (error "couldn't find loop header") $ mapLookup headerLabel blockMap
          CondBranch _ _ elbl _ = lastInst headerBlock

lastInst :: Block MidIRInst C C -> MidIRInst O C
lastInst block = case end of
                     JustC inst -> inst
    where (_, _, end) = blockToNodeList block
