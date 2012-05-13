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
          -- First pass, removes obviously non-parallel loops (such as loops that contain returns or callouts)
          noBreaksRetsCallsLoops = S.filter (\l -> noCalls l && noRets l && noBreaks l) loops 
          -- Second pass, removes loops that write to values that aren't loop invariant (i.e. for loops calculating a sum)
          noVariantWritesLoops = S.filter (\l -> noVariantWrites (loopVarInfos Map.! l) l) noBreaksRetsCallsLoops
          -- Third pass, removes all loops with cross-loop dependencies. This is the big one that involves solving some 
          -- equations. This should effectively return all of the parallelizable loops.
          parallelLoops = S.filter noCrossDependencies noVariantWritesLoops
          

          loopVarInfos = Map.fromList [(loop, findLoopVarInfo webs loop) | loop <- S.toList noBreaksRetsCallsLoops]

          -- Useful for debugging 
          loopVarNames :: LoopVarInfo -> (S.Set VarName, S.Set VarName) 
          loopVarNames (variant, invariant) = (S.map webIDToVarName variant, S.map webIDToVarName invariant) 
              where webIDToVarName id = webVar $ getWeb id webs 




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


          noVariantWrites :: LoopVarInfo -> Loop -> Bool 
          noVariantWrites (variant, invariant) loop = all noWritesInLoop $ S.toList variant
              where noWritesInLoop :: WebID -> Bool 
                    noWritesInLoop webID = S.null $ S.intersection allDefs (loop_body loop) 
                        where allDefs = S.map nodeLabel $ webDefs $ getWeb webID webs

          -- Simple Loop Nesting information 
          loopParents :: Map.Map Loop [Loop]
          loopParents = Map.fromList [(l, findLoopParents l) | l <- S.toList loops]
          
          findLoopParents :: Loop -> [Loop] 
          findLoopParents loop = [l | l <- S.toList loops, isLoopParent l]
              where header = loop_header loop
                    isLoopParent p = S.size (loop_body p) > S.size (loop_body loop) && S.member header (loop_body p)


          loopChildren :: Map.Map Loop [Loop] 
          loopChildren = Map.fromList [(l, findLoopChildren l) | l <- S.toList loops]

          findLoopChildren :: Loop -> [Loop]
          findLoopChildren loop = [l | l <- S.toList loops, isLoopChild l] 
              where isLoopChild c = S.size (loop_body c) < S.size (loop_body loop) && S.member (loop_header c) (loop_body loop)
                          
          noCrossDependencies :: Loop -> Bool 
          noCrossDependencies loop = all (noCrossDependency loop) $ potentialDependencies
              where (loads, stores) = findLoopLoadsAndStores loop graph 
                    potentialDependencies = S.toList $ S.union readWriteDeps writeWriteDeps 
                    readWriteDeps = S.fromList [(read, write) | read <- S.toList loads, write <- S.toList stores]
                    writeWriteDeps = S.fromList [(write1, write2) | write1 <- S.toList stores, write2 <- S.toList stores]
                    
          noCrossDependency :: Loop -> (MidIRExpr, MidIRExpr) -> Bool 
          noCrossDependency loop (expr1, expr2) 
              = case (findLabel expr1, findLabel expr2) of 
                  (Nothing, _) -> False 
                  (_, Nothing) -> False 
                  (Just l1, Just l2) 
                      | l1 /= l2 -> True 
                      | otherwise -> case (linConstExpr loop expr1, linConstExpr loop expr2) of 
                                       (Nothing, _) -> False 
                                       (_, Nothing) -> False 
                                       (Just linExpr1, Just linExpr2) -> solveLinExprs linExpr1 linExpr2 
              where v@(variant, invariant) = loopVarInfos Map.! loop 
                    (variantNames, invariantNames) = loopVarNames v 
                    
                    solveLinExprs :: MidIRExpr -> MidIRExpr -> Bool 
                    solveLinExprs expr1 expr2 = trace ("Dep: " ++ (show expr1) ++ ", " ++ (show expr2)) True

          -- Try to place the expression into linear constant form 
          -- where the expression represents a linear function of a number 
          -- of available loop induction variables. Returns Nothing if the 
          -- expression can't be placed in linear constant form
          linConstExpr :: Loop -> MidIRExpr -> Maybe MidIRExpr 
          linConstExpr loop expr = do newExpr <- return $ eliminateLabels expr 
                                      newExpr <- rejectObviousProblems newExpr
                                      case hasNonLoopVariables newExpr of 
                                        True -> do newExpr <- tryRemoveNonLoops newExpr
                                                   linConstExpr loop newExpr
                                        False -> rejectNonLinear newExpr
                                                 
              where v@(variants, invariants) = loopVarInfos Map.! loop 
                    (variantNames, invariantNames) = loopVarNames v 
                    varNameToWebID :: Map.Map VarName WebID 
                    varNameToWebID = Map.fromList [(webVar $ getWeb id webs, id) | id <- S.toList $ S.union variants invariants]
                    availableLoopVars :: S.Set VarName 
                    availableLoopVars = S.union myVariables $ S.union parentVars childVars 
                    parentVars = S.fromList [var | p <- loopParents Map.! loop, (var, _, _, _) <- loop_variables p] 
                    childVars = S.fromList [var | c <- loopChildren Map.! loop, (var, _, _, _) <- loop_variables c]
                    myVariables = S.fromList $ [var | (var, _, _, _) <- loop_variables loop]

                    rejectObviousProblems :: MidIRExpr -> Maybe MidIRExpr 
                    rejectObviousProblems expr
                        | fold_EE isObviousProblem False expr = Nothing 
                        | otherwise = Just expr

                    isObviousProblem :: Bool -> MidIRExpr -> Bool 
                    isObviousProblem b (LitLabel _ _) = True 
                    isObviousProblem b (Load _ _) = True 
                    isObviousProblem b (Cond _ _ _ _) = True
                    isObviousProblem b (Var _ v)
                        | S.member v variantNames = True
                    isObviousProblem b _ = b 

                    rejectNonLinear :: MidIRExpr -> Maybe MidIRExpr 
                    rejectNonLinear expr 
                        | fold_EE isNonLinear False expr = Nothing 
                        | otherwise = Just expr 

                    isNonLinear :: Bool -> MidIRExpr -> Bool 
                    isNonLinear b (BinOp _ OpMul (Var _ _) (Var _ _)) = True
                    isNonLinear b _ = b 

                    hasNonLoopVariables :: MidIRExpr -> Bool 
                    hasNonLoopVariables expr = fold_EE isNonLoopVar False expr 
                    isNonLoopVar :: Bool -> MidIRExpr -> Bool 
                    isNonLoopVar b (Var _ v) 
                        | S.notMember v availableLoopVars = True 
                    isNonLoopVar b _ = b 

                    tryRemoveNonLoops :: MidIRExpr -> Maybe MidIRExpr 
                    tryRemoveNonLoops expr = foldM removeNonLoop expr $ S.toList nonLoopVars
                        where nonLoopVars = fold_EE addNonLoopVars S.empty expr 
                              addNonLoopVars s (Var _ v) 
                                  | S.notMember v availableLoopVars = S.insert v s 
                              addNonLoopVars s _ = s
                              removeNonLoop :: MidIRExpr -> VarName -> Maybe MidIRExpr 
                              removeNonLoop expr v
                                  = let webID = varNameToWebID Map.! v 
                                        web = getWeb webID webs
                                        defs = webDefs web
                                        singleDef = head $ S.toList defs
                                        replaceInst = getNodeInstOO singleDef pGraph
                                    in if S.size defs /= 1 
                                       then Nothing 
                                       else case replaceInst of 
                                              Just (Store _ _ new) 
                                                  -> Just $ fromMaybe expr $ mapEE (replaceVar v new) expr   
                                              _ -> Nothing 

                              replaceVar :: VarName -> MidIRExpr -> MidIRExpr -> Maybe MidIRExpr 
                              replaceVar v expr (Var _ x) 
                                  | v == x = Just $ expr 
                              replaceVar _ _ _ = Nothing

          eliminateLabels :: MidIRExpr -> MidIRExpr 
          eliminateLabels expr = fromMaybe expr $ (mapEE maybeEliminateLabel) expr 
          maybeEliminateLabel (BinOp _ _ (LitLabel _ _) expr) = Just expr 
          maybeEliminateLabel (BinOp _ _ expr (LitLabel _ _)) = Just expr 
          maybeEliminateLabel _ = Nothing


          findLabel :: MidIRExpr -> Maybe String 
          findLabel (LitLabel _ s) = Just s 
          findLabel (Lit _ _) = Nothing 
          findLabel (Var _ _) = Nothing 
          findLabel (Load _ _) = Nothing 
          findLabel (UnOp _ _ expr) = findLabel expr 
          findLabel (BinOp _ _ expr1 expr2) = case findLabel expr1 of 
                                                Nothing -> findLabel expr2
                                                js -> js 
          findLabel (Cond _ expr1 expr2 expr3) 
              = case findLabel expr1 of 
                  Nothing -> case findLabel expr2 of 
                               Nothing -> findLabel expr3
                               js -> js 
                  js -> js 

-- LoopVarInfo represents a set of the variables that are variant in a loop and a set of the variables that are invariant in the loop
-- An easy way to throw out loops as non-parallel is if they contain any writes to variant loop values 
type LoopVarInfo = (S.Set WebID, S.Set WebID) 

findLoopVarInfo :: Webs -> Loop -> LoopVarInfo 
findLoopVarInfo webs loop = S.fold addVarWebs (S.empty, S.empty) loopWebs
    where body = loop_body loop 
          loopVars = loop_variables loop 
          loopWebs = websIntersectingBlocks webs body 
          -- Now that we have each web contained in the loop, time to determine if the webs are loop invariant or not
          addVarWebs :: WebID -> LoopVarInfo -> LoopVarInfo 
          addVarWebs webID (variant, invariant) 
              | isInvariant webID = (variant, S.insert webID invariant) 
              | otherwise = (S.insert webID variant, invariant)

          isInvariant :: WebID -> Bool 
          isInvariant webID = (webInBlocks web body) || (webIsCorrectLoopVariable web) 
              where web = getWeb webID webs 

          webIsCorrectLoopVariable :: Web -> Bool 
          webIsCorrectLoopVariable web
              | not ( (webVar web) `elem` [x | (x, _, _, _) <- loopVars] ) = False
              | S.size (webDefs web) /= 2 = False 
              | otherwise = True
                    
          
type LoadsAndStores = (S.Set MidIRExpr, S.Set MidIRExpr)

findLoopLoadsAndStores :: Loop -> Graph MidIRInst C C -> LoadsAndStores
findLoopLoadsAndStores loop graph = S.fold addLoadsAndStores (S.empty, S.empty) $ loop_body loop 
    where addLoadsAndStores :: Label -> LoadsAndStores -> LoadsAndStores 
          addLoadsAndStores label (loads, stores) = (addBlockLoads block loads, addBlockStores block stores) 
              where BodyBlock block = lookupBlock graph label 

          addBlockLoads :: Block MidIRInst C C -> S.Set MidIRExpr -> S.Set MidIRExpr 
          addBlockLoads block loads = loads'''
              where loads' = addLoads loads me 
                    loads'' = foldl addLoads loads' inner 
                    loads''' = addLoads loads'' mx 
                    (me', inner, mx') = blockToNodeList block 
                    me :: MidIRInst C O 
                    me = case me' of 
                           JustC x -> x 
                    mx :: MidIRInst O C
                    mx = case mx' of 
                           JustC x -> x

          addLoads :: S.Set MidIRExpr -> MidIRInst e x -> S.Set MidIRExpr
          addLoads set inst = fold_EN addLoadExpr set inst 

          addLoadExpr :: S.Set MidIRExpr -> MidIRExpr -> S.Set MidIRExpr 
          addLoadExpr set (Load _ expr) = S.insert expr set
          addLoadExpr set _ = set


          addBlockStores :: Block MidIRInst C C -> S.Set MidIRExpr -> S.Set MidIRExpr 
          addBlockStores block stores = foldl addStores stores inner 
              where (_, inner, _) = blockToNodeList block 

          addStores :: S.Set MidIRExpr -> MidIRInst O O -> S.Set MidIRExpr 
          addStores set (IndStore _ dest _) = S.insert dest set 
          addStores set _ = set

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
 