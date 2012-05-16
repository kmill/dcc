{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}
module Parallelize where 

import CLI
import Compiler.Hoopl
import Text.Parsec.Pos
import Data.Maybe
import LoopAnalysis
import IR
import DataflowTypes
import qualified Data.Set as S
import qualified Data.List as L
import Data.Int
import Data.List
import AST(noPosition)

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

performParallelizePass :: CompilerOpts -> MidIRRepr -> RM MidIRRepr
performParallelizePass opts midir
    = foldl (>>=) (return midir) $ map (forLoop defaultThreadMax) $ t $ L.sortBy compare' $ S.toList goodLoops
    where goodLoops = analyzeParallelizationPass midir
          defaultThreadMax = numThreads opts

-- Need to do some things here:
-- 1. Change loop header pred branch to instance of Parallel
-- 2. Change loop header conditional branch to jump to threadreturn
-- 3. Change counter increment
-- 4. Set loop variable to final value
forLoop :: Int -> Loop -> MidIRRepr -> RM MidIRRepr
forLoop defaultThreadMax loop midir = do
    donel <- freshLabel
    tret <- freshLabel
    loopl <- freshLabel
    i <- genTmpVar
    iend <- genTmpVar
    let [contl] = successors (fromJust $ mapLookup (loop_header loop) blockMap)
                  \\ S.toList (loop_body loop)
        pos = noPosition
        
        init = mkInitBlock loopl pos loop i
        doneBlock = mkDoneBlock pos donel contl iend loop
        threadret = blockOfNodeList
                    (JustC (Label pos tret), [], JustC (ThreadReturn pos donel))
        
        blockMap' = mapMap (updateIncBlock pos loop i threadMax) blockMap
        blockMap'' = mapMap (updateParBlock pos loop i threadMax loopl donel) blockMap'
        blockMap''' = mapInsert loopl init $
                      mapInsert donel doneBlock $
                      mapInsert tret threadret $ blockMap''

        blockMap'''' = mapMap (updateJumpOut pos loop tret) blockMap'''

        graph' = GMany NothingO blockMap'''' NothingO
    return $ midir { midIRGraph = graph' }
    where graph = midIRGraph midir
          GMany _ blockMap _ = graph
          threadMax = defaultThreadMax
--          blockMap' = parallelHeader threadMax (t loop) $ fixInc threadMax loop blockMap

mkInitBlock :: Label -> SourcePos -> Loop -> VarName -> Block MidIRInst C C
mkInitBlock lab pos loop i
    = blockOfNodeList ( JustC (Label pos lab)
                      , mkInits
                      , JustC (Branch pos (loop_header loop)))
    where mkInits = map mkInit $ S.toList $ loop_variables loop
          mkInit (var, start, _, step)
              = Store pos var (BinOp pos OpAdd
                               (evalFloatExpr pos start)
                               (BinOp pos OpMul
                                (Lit pos step) (Var pos i)))


mkDoneBlock :: SourcePos -> Label -> Label -> VarName -> Loop
            -> Block MidIRInst C C
mkDoneBlock pos donel contl endv loop
    = blockOfNodeList ( JustC (Label pos donel)
                      , [Store pos endv gend] ++ mkFins
                      , JustC (Branch pos contl))
    where gend = case loop_base loop of
                   (_, _, end, _) ->
                       BinOp pos OpAdd (Lit pos 1) (evalFloatExpr pos end)
          mkFins = map mkFin $ S.toList $ loop_variables loop
          mkFin (var, _, _, step)
              = Store pos var (BinOp pos OpMul (Lit pos step) (Var pos endv))

convertFloatExpr :: SourcePos -> FloatExpr -> Expr VarName
convertFloatExpr pos (ILit i) = Lit pos i
convertFloatExpr pos (FLit d) = Lit pos (floor d)
convertFloatExpr pos (FVar vn) = Var pos vn
convertFloatExpr pos (FUnOp op exp) = UnOp pos op (evalFloatExpr pos exp)
convertFloatExpr pos (FBinOp op exp1 exp2) = BinOp pos op
                                          (evalFloatExpr pos exp1)
                                          (evalFloatExpr pos exp2)

evalFloatExpr pos expr = convertFloatExpr pos $ floorFloatExpr (makeLinear expr)

updateParBlock :: SourcePos -> Loop -> VarName -> Int -> Label -> Label
               -> Block MidIRInst C C
               -> Block MidIRInst C C
updateParBlock pos loop i threadMax loopl contl block
    = if successors block == [loop_header loop]
         && entryLabel block `S.notMember` loop_body loop
      then blockOfNodeList ( JustC e
                           , inner
                           , JustC (Parallel pos loopl i threadMax contl))
      else block
    where (me, inner, mx) = blockToNodeList block
          e = (case me of 
                 JustC e' -> e') :: MidIRInst C O
          x = (case mx of 
                 JustC x' -> x') :: MidIRInst O C

updateIncBlock :: SourcePos -> Loop -> VarName -> Int -> Block MidIRInst C C
               -> Block MidIRInst C C
updateIncBlock pos loop i threadMax block
    = if entryLabel block `S.member` loop_body loop 
         && successors block == [loop_header loop]
      then blockOfNodeList (JustC e
                           ,inner
                            ++ [Store pos i (BinOp pos OpAdd
                                             (Lit pos $ fromIntegral threadMax)
                                             (Var pos i))]
                            ++ mkUpdates pos loop i threadMax, JustC x)
      else block
    where (me, inner, mx) = blockToNodeList block
          e = (case me of 
                 JustC e' -> e') :: MidIRInst C O
          x = (case mx of 
                 JustC x' -> x') :: MidIRInst O C

mkUpdates :: SourcePos -> Loop -> VarName -> Int -> [MidIRInst O O]
mkUpdates pos loop i threadMax 
    = map (\(var,_,_,step)
               -> Store pos var
                  (BinOp pos OpMul
                   (Lit pos step)
                   (Var pos i))) (S.toList $ loop_variables loop)

updateJumpOut :: SourcePos -> Loop -> Label -> Block MidIRInst C C
              -> Block MidIRInst C C
updateJumpOut pos loop lab block
    = if entryLabel block == loop_header loop
      then blockOfNodeList (JustC e, inner, JustC x')
      else block
    where (me, inner, mx) = blockToNodeList block
          e = (case me of 
                 JustC e' -> e') :: MidIRInst C O
          x = (case mx of 
                 JustC x' -> x') :: MidIRInst O C
          
          x' = (case x of
                  CondBranch pos exp l1 l2
                      | l1 `S.notMember` loop_body loop
                          -> CondBranch pos exp lab l2
                      | otherwise
                          -> CondBranch pos exp l1 lab
                  _ -> error "Loop header doesn't end in a cond branch")
               :: MidIRInst O C

-- -- returns looping variable, lower bound, upper bound, end label
-- loopData :: Loop -> MidIRMap -> (VarName, Int64, Int64, Label)
-- loopData loop blockMap = (var, lower, upper, elbl)
--     where (_, stores, _) = blockToNodeList $ headerPredBlock loop blockMap
--           firstLower :: [MidIRInst O O] -> Int64
--           firstLower [] = error "couldn't find upper bound"
--           firstLower ((Store _ var' (Lit _ lower))  : xs)
--               | var' == var = lower
--               | otherwise = firstLower xs
--           firstLower (x : xs) = ts x $ firstLower xs
--           lower = firstLower $ reverse $ t stores
--           (var, upper, elbl)
--               = (case lastInst $ headerBlock loop blockMap of
--                   CondBranch _ (BinOp _ CmpGTE (Var _ var) (Lit _ upper)) elbl _
--                         -> (var, upper, elbl)
--                   _ -> error "this shoul be a condbranch") :: (VarName, Int64, Label)

-- parallelHeader :: Int -> Loop -> MidIRMap -> MidIRMap
-- parallelHeader threadMax loop blockMap
--     = mapInsert headerPredLabel headerPredBlock' $ mapDelete headerPredLabel blockMap
--     where headerLabel = loop_header loop
--           headerPredLabel = headerPred loop blockMap
--           headerPredBlock' = mapBlock processHeader $ headerPredBlock loop blockMap
--           processHeader :: forall e x. MidIRInst e x -> MidIRInst e x
--           processHeader inst@(Branch pos lbl)
--               | lbl == headerLabel
--                   = Parallel pos headerLabel var threadMax elbl
--               | otherwise = error "Branch not to loop header"
--           processHeader inst = inst
--           (var, _, _, elbl) = t $ loopData loop blockMap

-- getBlock :: Label -> MidIRMap -> Block MidIRInst C C
-- getBlock label
--     = mapFindWithDefault 
--         (error $ "couldn't find block at " ++ (show label))
--         label

-- headerPredBlock :: Loop -> MidIRMap -> Block MidIRInst C C
-- headerPredBlock loop blockMap = getBlock (headerPred loop blockMap) blockMap

-- headerPred :: Loop -> MidIRMap -> Label
-- headerPred loop blockMap
--     = head $ map fst $ filter (elem lbl . successors . snd) loopList
--     where lbl = loop_header loop
--           loopList = filter (\(l, b) -> S.notMember l $ loop_body loop) list
--           list = mapToList blockMap

-- headerBlock :: Loop -> MidIRMap -> Block MidIRInst C C
-- headerBlock loop blockMap = getBlock (loop_header loop) blockMap

-- -- returns ONE loop predecessor. is UNCHECKED whether there are more.
-- loopPred :: Loop -> MidIRMap -> Label -> Label
-- loopPred loop blockMap lbl
--     = head $ map fst $ filter (elem lbl . successors . snd) loopList
--     where list = mapToList blockMap
--           loopList = filter (\(l, b) -> S.member l $ loop_body loop) list

-- -- takes maximum number of threads
-- fixInc :: Int -> Loop -> MidIRMap -> MidIRMap
-- fixInc threadMax loop blockMap
--     = mapInsert incLabel incBlock' $ mapDelete incLabel blockMap
--     where headerLabel = loop_header loop
--           incLabel = loopPred loop blockMap headerLabel
--           incBlock = getBlock incLabel blockMap
--           incBlock' = mapBlock processInc incBlock
--           processInc :: forall e x. MidIRInst e x -> MidIRInst e x
--           processInc (Store posS var' _)
--               | var'
--               | (var' == var) && (lit' == 1) && (var'' == var)
--                   = (Store posS var (BinOp posO OpAdd (Var posV var) (Lit posL $ fromIntegral threadMax)))
--               | otherwise = error "Error in loop processing :-("
--           processInc inst = inst
--           (var, _, _, inc) = loopData loop blockMap
--           incMap = 

-- lastInst :: Block MidIRInst C C -> MidIRInst O C
-- lastInst block = case end of
--                      JustC inst -> inst
--     where (_, _, end) = blockToNodeList block

-- threadReturn :: Label -> Label -> Loop -> MidIRMap -> MidIRMap
-- threadReturn rlbl prlbl loop blockMap
--     = mapInsert prlbl postReturnBlock $ mapInsert rlbl returnBlock $ mapInsert headerLabel headerBlock' blockMap
--     where headerLabel = loop_header loop
--           headerBlock' = mapBlock process $ headerBlock loop blockMap
--           process :: forall e x. MidIRInst e x -> MidIRInst e x
--           process (CondBranch pos expr elbl llbl)
--               = CondBranch pos expr rlbl llbl
--           process inst = inst
--           (var, _, upper, elbl) = loopData loop blockMap
--           pos = newPos "" 0 0
--           returnBlock = blockOfNodeList (JustC (Label pos rlbl), [], JustC (ThreadReturn pos prlbl))
--           postReturnNodes = [Store pos var (Lit pos upper)]
--           postReturnBlock = blockOfNodeList (JustC (Label pos prlbl), postReturnNodes, JustC (Branch pos elbl))
