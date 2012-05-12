{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}
module LoopAnalysis where 

import Dataflow.Dominator 
import Dataflow.OptSupport
import Dataflow.IRWebs
import DataflowTypes

import Compiler.Hoopl
import Compiler.Hoopl.Fuel
import Debug.Trace
import IR

import Control.Monad


import Util.NodeLocate

import Data.Int
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as Map





data Loop = Loop { loop_header :: Label 
                 , loop_body :: S.Set Label
                 , loop_variables :: [LoopVariable] }
            deriving (Eq, Ord, Show)

type BackEdge = (Label, Label)
type LoopVariable = (VarName, MidIRExpr, MidIRExpr, Int64)

midirLoops :: MidIRRepr -> S.Set Loop
midirLoops midir = findLoops domins graph mlabels
    where graph = midIRGraph midir
          mlabels = map methodEntry $ midIRMethods midir
          domins = findDominators graph mlabels

data LoopNest = LoopNest Loop LoopNest 
              | LeafLoop Loop 
                deriving (Eq, Ord, Show)

listToLoopNest :: [Loop] -> LoopNest 
listToLoopNest [] = error "attempted to create loop nest from empty list :-{"
listToLoopNest (x:[]) = LeafLoop x
listToLoopNest (x:xs) = LoopNest x $ listToLoopNest xs

loopNestToList :: LoopNest -> [Loop] 
loopNestToList (LeafLoop l) = [l]
loopNestToList (LoopNest l n) = l:(loopNestToList n)


findLoops :: FactBase DominFact -> Graph MidIRInst C C -> [Label] -> S.Set Loop 
findLoops dominators graph mlabels = S.fromList loops
    where GMany _ body _ = graph
          backEdges = findBackEdges dominators (mapElems body)
          loops = map (backEdgeToLoop dominators graph mlabels) backEdges


findBackEdges :: NonLocal n => FactBase DominFact -> [Block n C C] -> [BackEdge]
findBackEdges _ [] = []
findBackEdges dominators (x:xs) = case mapLookup (entryLabel x) dominators of 
                                    Just (PElem domin) -> (maybeBackEdges domin) ++ (findBackEdges dominators xs)
                                    _ -> findBackEdges dominators xs
    where maybeBackEdges domin = [ (entryLabel x, y) | y <- successors x, S.member y domin]

backEdgeToLoop :: FactBase DominFact -> Graph MidIRInst C C -> [Label] -> BackEdge -> Loop 
backEdgeToLoop dominators graph mlabels (loopBack, loopHeader) = Loop loopHeader loopBody loopVariables
    where loopBody = S.insert loopHeader $ findReaching loopBack loopHeader graph mlabels
          headerDomins = case mapLookup loopHeader dominators of 
                           Just (PElem domin) -> domin
                           _ -> S.empty
          BodyBlock loopBackBlock = lookupBlock graph loopBack
          BodyBlock headerBlock = lookupBlock graph loopHeader
          loopVariables = findLoopVariables graph headerDomins headerBlock loopBackBlock
         
                    

findLoopVariables :: Graph MidIRInst C C -> S.Set Label -> Block MidIRInst C C -> Block MidIRInst C C -> [LoopVariable]
findLoopVariables graph headerDomin headerBlock loopbackBlock 
    = loopVariables
    where (_, inner, _) = blockToNodeList loopbackBlock 
          loopVariables = findLoopVarNames inner
          findLoopVarNames :: [MidIRInst e x] -> [LoopVariable]
          findLoopVarNames [] = []
          findLoopVarNames (Store _ v expr:xs)
              | isJust $ makeLoopVariable v expr = (fromJust $ makeLoopVariable v expr):(findLoopVarNames xs) 
          findLoopVarNames (_:xs) = findLoopVarNames xs

          makeLoopVariable :: VarName -> MidIRExpr -> Maybe LoopVariable
          makeLoopVariable v expr  
              = do varFinalValue <- findFinalValue v 
                   incValue <- findIncValue v expr 
                   varInitValue <- findInitValue v
                   return (v, varInitValue, varFinalValue, incValue)

          -- To find the init value for a loop, we're going to have to look at the predecessors to the loop 
          -- header. If we find more than one potential value, then we can't parallelize so just discard the loop
          -- (i.e. return Nothing)
          -- Can't look at the predecessors, so we're going to look at the dominators instead
          -- specifically, want to find a list of all the definitions of the variable in 
          -- the dominators of the header. Hopefully there will only be one
          findInitValue :: VarName -> Maybe MidIRExpr
          findInitValue v = case varDefs of 
                              x:[] -> Just x
                              _ -> Nothing 
              where varDefs = concatMap (findVarDefs v) $ S.toList headerDomin
                   
          findVarDefs :: VarName -> Label -> [MidIRExpr]
          findVarDefs v l = let BodyBlock block = lookupBlock graph l
                                (_, inner, _) = blockToNodeList block
                                in [expr | (Store _ x expr) <- inner, x == v]

          -- To find the final value for a loop, we're going to have to look at the loop header
          -- need to look until we find a statement of the pattern 
          -- (CondBranch _ (BinOp _ CmpGTE (Var _ v) (Lit _ i)) tl fl)
          -- The final value is then i 
          findFinalValue :: VarName -> Maybe MidIRExpr
          findFinalValue v = case headerX of 
                               JustC (CondBranch _ (BinOp _ CmpGTE (Var _ x) expr) _ _)
                                   | x == v -> Just expr
                               _ -> Nothing
              where (_, _, headerX) = blockToNodeList headerBlock

          findIncValue :: VarName -> MidIRExpr -> Maybe Int64
          findIncValue v (BinOp _ OpAdd (Var _ x) (Lit _ i)) =  Just i
          findIncValue v (BinOp _ OpAdd (Lit _ i) (Var _ x)) =  Just i 
          findIncValue v _ = Nothing

      

analyzeParallelizationPass :: MidIRRepr -> S.Set Loop 
analyzeParallelizationPass midir = parallelLoops
    where loops = findLoops domins graph mlabels
          parallelLoops = maybeParallelLoops
          -- First pass, removes obviously non-parallel loops (such as loops that contain returns or callouts)
          maybeParallelLoops = S.filter (\l -> noCalls l && noRets l && noBreaks l) loops 
          graph = midIRGraph midir
          pGraph = toPGraph graph
          webs = getWebs mlabels pGraph
          mlabels = (map methodEntry $ midIRMethods midir)
          domins = findDominators graph mlabels

          noCalls :: Loop -> Bool 
          noCalls (Loop header body _) = all noCall $ S.toList body 
              where noCall :: Label -> Bool 
                    noCall l = let BodyBlock block = lookupBlock graph l 
                                   (_, inner, mx) = blockToNodeList block
                                   in (all notACall inner) || isAFail mx  

          notACall :: MidIRInst O O -> Bool 
          notACall (Call _ _ _ _) = False
          notACall (Callout _ _ _ _) = False 
          notACall _ = True

          isAFail :: MaybeC C (MidIRInst O C) -> Bool 
          isAFail (JustC (Fail _)) = True 
          isAFail _ = False

          noRets :: Loop -> Bool 
          noRets (Loop _ body _) = all noRet $ S.toList body 
              where noRet :: Label -> Bool 
                    noRet l = let BodyBlock block = lookupBlock graph l 
                                  (_, _, mx) = blockToNodeList block 
                                  in notARet mx 

          notARet :: MaybeC C (MidIRInst O C) -> Bool 
          notARet (JustC (Return _ _ _)) = False 
          notARet _ = True 
          
          noBreaks :: Loop -> Bool 
          noBreaks (Loop header body _) = all noBreak $ S.toList body  
              where noBreak :: Label -> Bool 
                    noBreak l 
                        | l == header = True 
                        | otherwise = let BodyBlock block = lookupBlock graph l 
                                      in all (\s -> S.member s body) $ successors block
          

-- LoopVarInfo represents a set of the variables that are invariant in a loop and a set of the variables that are variant in the loop
-- An easy way to throw out loops as non-parallel is if they contain any writes to variant loop values 
type LoopVarInfo = (S.Set WebID, S.Set WebID) 

findLoopVarInfo :: Webs -> Graph (PNode MidIRInst) C C -> Loop -> LoopVarInfo 
findLoopVarInfo webs pGraph loop = error "Not yet implemented :-{"
    where body = loop_body loop 
          loopVars = loop_variables loop 
          loopWebs = websIntersectingBlocks webs body 
                    
          
          



createLoopNests :: S.Set Loop -> [LoopNest] 
createLoopNests loops = error "Not yet implemented :-{"
          




findDominators :: forall n. NonLocal n => Graph n C C -> [Label] -> FactBase DominFact 
findDominators graph mlabels = domins 
     where (_, domins, _) = runGM domins'
          --domins' :: GM (Graph n C C, FactBase DominFact, MaybeO C DominFact)
           dominAnalysis :: RM (Graph n C C, FactBase DominFact, MaybeO C DominFact)
           dominAnalysis = (analyzeAndRewriteFwd 
                            generalDominPass 
                            (JustC mlabels)
                            graph
                            (mapFromList (map (\l -> (l, fact_bot dominatorLattice)) mlabels)))
           domins' = runWithFuel 2222222 dominAnalysis

generalDominPass :: (CheckpointMonad m, FuelMonad m, UniqueNameMonad m, NonLocal n)
                 => FwdPass m n DominFact 
generalDominPass = FwdPass 
                   { fp_lattice = dominatorLattice
                   , fp_transfer = generalDominAnalysis
                   , fp_rewrite = noFwdRewrite }

type LoopBody = S.Set Label

loopNestInformation :: forall n. NonLocal n => Graph n C C -> [Label] -> Map.Map Label Int 
loopNestInformation graph mlabels = finalNestMap
    where domins = findDominators graph mlabels
          GMany _ body _ = graph 
          backEdges = findBackEdges domins (mapElems body)
          loops = map (findLoopBodies graph) backEdges

          -- Now that all information is available, populate the map with our information
          finalNestMap = foldl addLoopNests Map.empty loops

          addLoopNests :: Map.Map Label Int -> S.Set Label -> Map.Map Label Int
          addLoopNests nestMap s = S.fold addLoopNest nestMap s

          addLoopNest :: Label -> Map.Map Label Int -> Map.Map Label Int 
          addLoopNest l nestMap = case Map.lookup l nestMap of 
                                    Just i -> Map.insert l (i+1) nestMap
                                    Nothing -> Map.insert l 1 nestMap

          findLoopBodies :: Graph n C C -> BackEdge -> LoopBody
          findLoopBodies graph (loopBack, loopHeader) = S.insert loopHeader loopBody 
              where loopBody = findReaching loopBack loopHeader graph mlabels

          -- loops = findGeneralLoops domins graph




findReaching :: forall n. NonLocal n => Label -> Label -> Graph n C C -> [Label] -> S.Set Label 
findReaching loopBack loopHeader graph mlabels 
    = failReaching
      where (_, reaching, _) = runGM reaching' 
            reachingRun :: RM (Graph n C C, FactBase ReachingFact, MaybeO C ReachingFact)
            reachingRun = (analyzeAndRewriteBwd
                           reachingPass
                           (JustC mlabels)
                           graph
                           mapEmpty)
            reaching' = runWithFuel 2222222 reachingRun
            reachingPass = BwdPass reachingLattice (reachingAnalysis loopBack loopHeader) noBwdRewrite
            initialReaching = S.fromList [l | (l, b) <- mapToList reaching, b == True]
            failReaching = S.fold addClosedSuccs initialReaching initialReaching
            addClosedSuccs :: Label -> S.Set Label -> S.Set Label
            addClosedSuccs l set = foldl addClosedSucc set mySuccessors 
                where BodyBlock currentBlock = lookupBlock graph l  
                      mySuccessors = successors currentBlock 

            addClosedSucc :: S.Set Label -> Label -> S.Set Label
            addClosedSucc set l = if noSuccessors 
                                  then S.insert l set 
                                  else set
                where BodyBlock currentBlock = lookupBlock graph l
                      noSuccessors = null $ successors currentBlock
                                      

--dominatorTransfer :: Label -> (Map.Map Label (S.Set Label), Bool) -> (Map.Map Label 

type ReachingFact = Bool 
reachingLattice :: DataflowLattice ReachingFact 
reachingLattice = DataflowLattice { fact_name = "Reaching Fact"
                                  , fact_bot = False
                                  , fact_join = unionFact }
    where unionFact :: Label -> OldFact ReachingFact -> NewFact ReachingFact -> (ChangeFlag, ReachingFact)
          unionFact _ (OldFact old) (NewFact new) 
              = ( ch, old || new) 
                where ch = changeIf $ (old || new) /= old

reachingAnalysis :: forall n. (NonLocal n) => Label -> Label -> BwdTransfer n ReachingFact 
reachingAnalysis loopBack loopHeader = mkBTransfer3 bBegin bMiddle bEnd
    where bBegin :: n C O -> ReachingFact -> ReachingFact 
          bBegin inst f
              | entryLabel inst == loopBack = True
              | entryLabel inst == loopHeader = False 
              | otherwise = f

          bMiddle :: n O O -> ReachingFact -> ReachingFact 
          bMiddle inst f = f 

          bEnd :: n O C -> FactBase ReachingFact -> ReachingFact 
          bEnd inst f = or $ map (successorFact f) $ successors inst 

          successorFact factBase l = case mapLookup l factBase of 
                                       Just b -> b 
                                       Nothing -> False
 
