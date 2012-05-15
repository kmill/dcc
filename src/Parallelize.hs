{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}
module Parallelize where 

import Compiler.Hoopl
import Text.Parsec.Pos
import Data.Maybe
import LoopAnalysis
import IR
import DataflowTypes
import qualified Data.Set as S
import qualified Data.List as L
import Data.Int

import Debug.Trace

type MidIRMap = LabelMap (Block MidIRInst C C)

ts :: (Show a) => a -> b -> b
--ts = traceShow
ts a = id
t :: (Show a) => a -> a
t x = ts x x

compare' :: Loop -> Loop -> Ordering
compare' loop1 loop2 =
    case compareBodies of
        EQ -> compare loop1 loop2
        res -> res
    where compareBodies = compare (S.size $ loop_body loop1) (S.size $ loop_body loop2)

performParallelizePass :: MidIRRepr -> RM MidIRRepr
performParallelizePass midir = foldl (>>=) (return midir) $ map forLoop $ t $ L.sortBy compare' $ S.toList goodLoops
    where goodLoops = midirLoops midir -- analyzeParallelizationPass midir

defaultThreadMax :: Int64
defaultThreadMax = 10

-- Need to do some things here:
-- 1. Change loop header pred branch to instance of Parallel
-- 2. Change loop header conditional branch to jump to threadreturn
-- 3. Change counter increment
forLoop :: Loop -> MidIRRepr -> RM MidIRRepr
forLoop loop midir = do
    rlbl <- freshLabel
    let blockMap'' = threadReturn rlbl loop blockMap'
        graph' = GMany NothingO blockMap'' NothingO
    return $ midir { midIRGraph = graph' }
    where graph = midIRGraph midir
          GMany _ blockMap _ = graph
          blockMap' = parallelHeader (t loop) $ fixInc defaultThreadMax loop blockMap

-- returns looping variable, lower bound, upper bound, end label
loopData :: Loop -> MidIRMap -> (VarName, Int64, Int64, Label)
loopData loop blockMap = (var, lower, upper, elbl)
    where (_, stores, _) = blockToNodeList $ headerPredBlock loop blockMap
          firstLower :: [MidIRInst O O] -> Int64
          firstLower [] = error "couldn't find upper bound"
          firstLower ((Store _ var' (Lit _ lower))  : xs)
              | var' == var = lower
              | otherwise = firstLower xs
          firstLower (x : xs) = ts x $ firstLower xs
          lower = firstLower $ reverse $ t stores
          CondBranch _ (BinOp _ CmpGTE (Var _ var) (Lit _ upper)) elbl _
              = lastInst $ headerBlock loop blockMap

parallelVar :: Loop -> VarName
parallelVar loop = MV $ "idx_" ++ (show $ loop_header loop)

parallelHeader :: Loop -> MidIRMap -> MidIRMap
parallelHeader loop blockMap
    = mapInsert headerPredLabel headerPredBlock' $ mapDelete headerPredLabel blockMap
    where headerLabel = loop_header loop
          headerPredLabel = headerPred loop blockMap
          headerPredBlock' = mapBlock processHeader $ headerPredBlock loop blockMap
          processHeader :: forall e x. MidIRInst e x -> MidIRInst e x
          processHeader inst@(Branch pos lbl)
              | lbl == headerLabel
                  = Parallel pos headerLabel (parallelVar loop) lower upper 
              | otherwise = error "Branch not to loop header"
          processHeader inst = inst
          (_, lower, upper, _) = t $ loopData loop blockMap

getBlock :: Label -> MidIRMap -> Block MidIRInst C C
getBlock label
    = mapFindWithDefault 
        (error $ "couldn't find block at " ++ (show label))
        label

headerPredBlock :: Loop -> MidIRMap -> Block MidIRInst C C
headerPredBlock loop blockMap = getBlock (headerPred loop blockMap) blockMap

headerPred :: Loop -> MidIRMap -> Label
headerPred loop blockMap
    = head $ map fst $ filter (elem lbl . successors . snd) loopList
    where lbl = loop_header loop
          loopList = filter (\(l, b) -> S.notMember l $ loop_body loop) list
          list = mapToList blockMap

headerBlock :: Loop -> MidIRMap -> Block MidIRInst C C
headerBlock loop blockMap = getBlock (loop_header loop) blockMap

-- returns ONE loop predecessor. is UNCHECKED whether there are more.
loopPred :: Loop -> MidIRMap -> Label -> Label
loopPred loop blockMap lbl
    = head $ map fst $ filter (elem lbl . successors . snd) loopList
    where list = mapToList blockMap
          loopList = filter (\(l, b) -> S.member l $ loop_body loop) list

-- takes maximum number of threads
fixInc :: Int64 -> Loop -> MidIRMap -> MidIRMap
fixInc threadMax loop blockMap
    = mapInsert incLabel incBlock' $ mapDelete incLabel blockMap
    where headerLabel = loop_header loop
          incLabel = loopPred loop blockMap headerLabel
          incBlock = getBlock incLabel blockMap
          incBlock' = mapBlock processInc incBlock
          processInc :: forall e x. MidIRInst e x -> MidIRInst e x
          processInc (Store posS var' (BinOp posO OpAdd (Lit posL lit') (Var posV var'') ))
              | (var' == var) && (lit' == 1) && (var'' == var)
                  = (Store posS var (BinOp posO OpAdd (Var posV var) (Lit posL threadMax)))
              | otherwise = error "Error in loop processing :-("
          processInc inst = inst
          (var, _, _, _) = loopData loop blockMap

lastInst :: Block MidIRInst C C -> MidIRInst O C
lastInst block = case end of
                     JustC inst -> inst
    where (_, _, end) = blockToNodeList block

threadReturn :: Label -> Loop -> MidIRMap -> MidIRMap
threadReturn rlbl loop blockMap
    = mapInsert rlbl returnBlock $ mapInsert headerLabel headerBlock' $ mapDelete headerLabel blockMap
    where headerLabel = loop_header loop
          headerBlock' = mapBlock process $ headerBlock loop blockMap
          process :: forall e x. MidIRInst e x -> MidIRInst e x
          process (CondBranch pos expr elbl llbl)
              = CondBranch pos expr rlbl llbl
          process inst = inst
          (_, _, _, elbl) = loopData loop blockMap
          pos = newPos "" 0 0
          returnBlock = blockOfNodeList (JustC (Label pos rlbl), [], JustC (ThreadReturn pos elbl))
