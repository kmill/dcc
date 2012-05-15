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
import qualified Control.Monad.LPMonad as LP
import Data.LinearProgram.GLPK.Solver
import Data.LinearProgram.Common
import Data.Algebra
import System.IO.Unsafe

import Util.NodeLocate

import Text.ParserCombinators.Parsec.Pos (newPos, SourcePos)

import Data.Int
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as Map


-- To be completely general for dependency analysis, we put expressions into 
-- this form that can potentially include floating point numbers. 
-- This allows us to more generally solve looping equations.
data FloatExpr = ILit Int64
               | FLit Double 
               | FVar VarName 
               | FUnOp UnOp FloatExpr 
               | FBinOp BinOp FloatExpr FloatExpr 
                 deriving (Eq, Ord)

instance Show FloatExpr where 
    showsPrec _ (ILit x) = shows x 
    showsPrec _ (FLit x) = shows x
    showsPrec _ (FVar v) = shows v 
    showsPrec p (FUnOp op expr) = showParen (p>0) (shows op . showString " " . showsPrec 1 expr)
    showsPrec p (FBinOp op ex1 ex2)
        = showParen (p>0) (showsPrec 1 ex1 . showString " " . shows op . showString " " . showsPrec 1 ex2)

exprToFloatExpr :: MidIRExpr -> Maybe FloatExpr 
exprToFloatExpr (Lit _ i) = Just $ ILit i 
exprToFloatExpr (Var _ v) = Just $ FVar v 
exprToFloatExpr (UnOp _ op expr) 
    | op == OpNeg = do expr' <- exprToFloatExpr expr 
                       return $ (FUnOp op expr')
exprToFloatExpr (BinOp _ op expr1 expr2) 
    | op == OpAdd || op == OpSub || op == OpMul 
        = do expr1' <- exprToFloatExpr expr1
             expr2' <- exprToFloatExpr expr2
             return $ FBinOp op expr1' expr2'
exprToFloatExpr _ = Nothing

fold_FEE :: (a -> FloatExpr -> a) -> a -> FloatExpr -> a 
fold_FEE f z e@(ILit _) = f z e 
fold_FEE f z e@(FLit _) = f z e 
fold_FEE f z e@(FVar _) = f z e 
fold_FEE f z e@(FUnOp _ expr) = f (fold_FEE f z expr) e 
fold_FEE f z e@(FBinOp _ expr1 expr2) = f (fold_FEE f (fold_FEE f z expr2) expr1) e 

mapFEE :: MaybeChange FloatExpr -> MaybeChange FloatExpr 
mapFEE f e@(ILit _) = f e 
mapFEE f e@(FLit _) = f e 
mapFEE f e@(FVar _) = f e 
mapFEE f e@(FUnOp op expr) 
    = case mapFEE f expr of 
        Nothing -> f e 
        Just expr' -> Just $ fromMaybe e' (f e') 
            where e' = FUnOp op expr'
mapFEE f e@(FBinOp op e1 e2) 
    = case (mapFEE f e1, mapFEE f e2) of 
        (Nothing, Nothing) -> f e 
        (e1', e2') -> Just $ fromMaybe e' (f e') 
            where e' = FBinOp op (fromMaybe e1 e1') (fromMaybe e2 e2')

-- required for using Int64s as coefficients in a LP 
instance Group Int64 where 
    zero = 0 
    (^+^) = (+)
    (^-^) = (-) 
    neg x = (-x)

instance Ring Int64 where 
    one = 1 
    (*#) = (*)


data Loop = Loop { loop_header :: Label 
                 , loop_body :: S.Set Label
                 , loop_variables :: [LoopVariable] }
            deriving (Eq, Ord, Show)

type BackEdge = (Label, Label)
type LoopVariable = (VarName, MidIRExpr, MidIRExpr, Int64)

type IndVar = (VarName, FloatExpr, FloatExpr, Int64) 

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


dsp :: SourcePos 
dsp = newPos "" (-1) (-1) 

-- Returns whether a node dominates another node 
dominatesNode :: FactBase DominFact -> NodePtr -> NodePtr -> Bool
dominatesNode domins (NodePtr l1 o1) (NodePtr l2 o2) 
    | l1 /= l2 = S.member l1 dominLabel2
    | otherwise = o1 <= o2
    where dominLabel2 = case mapLookup l2 domins of 
                          Just (PElem d) -> d 
                          _ -> S.empty


findLoops :: FactBase DominFact -> Graph MidIRInst C C -> [Label] -> S.Set Loop 
findLoops dominators graph mlabels = S.fromList loops
    where GMany _ body _ = graph
          backEdges = findBackEdges dominators (mapElems body)
          loops = map (backEdgeToLoop dominators graph mlabels) backEdges

findLoopsSilly :: FactBase DominFact -> Graph MidIRInst C C -> [Label] -> S.Set (Loop, Label) 
findLoopsSilly dominators graph mlabels = S.fromList loops
    where GMany _ body _ = graph
          backEdges = findBackEdges dominators (mapElems body)
          loops = map (\(b, h) -> (backEdgeToLoop dominators graph mlabels (b, h), b)) backEdges


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
         
type BasicLoop = (Label, Label, S.Set Label)
data InductionLoc = Beginning | End deriving (Eq, Show)

findInductionVariables :: Graph (PNode MidIRInst) C C -> [Label] -> FactBase DominFact -> Webs -> BasicLoop -> S.Set IndVar
findInductionVariables pGraph mlabels domins webs (header, loopBack, body)
    = case trace (show limitVar) limitVar of 
        Nothing -> S.empty
        Just lv -> trace (show basicInductionVars) $ makeRestOfTheVariables lv (makeBaseVar lv)
    where loopWebs = websIntersectingBlocks webs body 
          -- Now that we have a list of the webs, look at each one and determine if it's an induction variable
          basicInductionVars = S.fromList $ catMaybes [makeInductionVar $ getWeb x webs | x <- S.toList loopWebs]
          varNameToInfo = Map.fromList [(v, a) | a@(v, _, _) <- S.toList basicInductionVars]
          basicIndNames = S.map (\(a, _, _) -> a) basicInductionVars
          BodyBlock headerBlock = lookupBlock pGraph header 
          (_, _, mx') = blockToNodeList headerBlock 
          mx :: MidIRInst O C 
          mx = case mx' of 
                 JustC (PNode _ x) -> x 

          makeRestOfTheVariables lv bv = S.insert lv $ S.insert bv $ S.fromList $ otherVars
              where otherVars = catMaybes [finishIndVar x lv bv | x <- S.toList $ basicInductionVars]
          
          finishIndVar (n, init, inc) (lv, _, _, _) (bv, _, _, _)
              | n == lv || n == bv = Nothing
          finishIndVar (n, init, inc) _ (_, _, iEnd, _) = Just (n, init, end, inc) 
              where end = FBinOp OpAdd (FBinOp OpMul (ILit inc) iEnd) init

          -- Let's see if we can find the loop limit induction variable which will help us determine our upper bounds
          limitVar :: Maybe IndVar 
          limitVar = case mx of 
                       CondBranch _ expr tl fl
                           | S.member fl body -> makeLimitVar expr
                           | S.member tl body -> makeReverseLimitVar expr 
                       _ -> Nothing 

          makeLimitVar :: MidIRExpr -> Maybe IndVar
          makeLimitVar (BinOp _ CmpGTE (Var _ v) expr)
              = do fExpr <- exprToFloatExpr expr 
                   (v, init, inc) <- Map.lookup v varNameToInfo
                   guard $ inc > 0
                   return (v, init, minOne fExpr, inc)
          makeLimitVar (BinOp _ CmpGT (Var _ v) expr)
              = do fExpr <- exprToFloatExpr expr 
                   (v, init, inc) <- Map.lookup v varNameToInfo
                   guard $ inc > 0 
                   return (v, init, fExpr, inc) 
          makeLimitVar (BinOp _ CmpLTE (Var _ v) expr) 
              = do fExpr <- exprToFloatExpr expr 
                   (v, init, inc) <- Map.lookup v varNameToInfo 
                   guard $ inc < 0 
                   return (v, init, plusOne fExpr, inc)
          makeLimitVar (BinOp _ CmpLT (Var _ v) expr) 
              = do fExpr <- exprToFloatExpr expr 
                   (v, init, inc) <- Map.lookup v varNameToInfo 
                   guard $ inc < 0 
                   return (v, init, fExpr, inc)
          makeLimitVar (BinOp _ CmpGTE expr (Var _ v)) 
              = makeLimitVar (BinOp dsp CmpLTE (Var dsp v) expr)
          makeLimitVar (BinOp _ CmpGT expr (Var _ v))
              = makeLimitVar (BinOp dsp CmpLT (Var dsp v) expr) 
          makeLimitVar (BinOp _ CmpLTE expr (Var _ v)) 
              = makeLimitVar (BinOp dsp CmpGTE (Var dsp v) expr)
          makeLimitVar (BinOp _ CmpLT expr (Var _ v)) 
              = makeLimitVar (BinOp dsp CmpGT (Var dsp v) expr) 
          makeLimitVar _ = Nothing

          makeReverseLimitVar (BinOp s CmpGTE e1 e2) 
              = makeLimitVar (BinOp s CmpLT e1 e2) 
          makeReverseLimitVar (BinOp s CmpGT e1 e2) 
              = makeLimitVar (BinOp s CmpLTE e1 e2) 
          makeReverseLimitVar (BinOp s CmpLTE e1 e2) 
              = makeLimitVar (BinOp s CmpGT e1 e2) 
          makeReverseLimitVar (BinOp s CmpLT e1 e2) 
              = makeLimitVar (BinOp s CmpGTE e1 e2)

          headerDomins = case mapLookup header domins of 
                           Just (PElem domin) -> domin
                           _ -> S.empty 

          backDomins = case mapLookup loopBack domins of 
                         Just (PElem domin) -> domin 
                         _ -> S.empty

          makeInductionVar :: Web -> Maybe (VarName, FloatExpr, Int64)
          makeInductionVar web 
              | (S.size $ webDefs web) /= 2 = Nothing
              | otherwise = let [def1, def2] = S.toList $ webDefs web
                                varName = webVar web
                            in case (inductionStart def1, inductionStep web def2) of 
                                 (Just init, Just (inc, End)) -> Just (varName, init, inc)
                                 (Just init, Just (inc, Beginning)) -> Just (varName, addF init (ILit inc), inc)
                                 _ -> case (inductionStart def2, inductionStep web def1) of 
                                        (Just init, Just (inc, End)) -> Just (varName, init, inc)
                                        (Just init, Just (inc, Beginning)) -> Just (varName, addF init (ILit inc), inc)
                                        _ -> Nothing 

          addF :: FloatExpr -> FloatExpr -> FloatExpr 
          addF f1 f2 = FBinOp OpAdd f1 f2

          minOne :: FloatExpr -> FloatExpr 
          minOne f = FBinOp OpSub f (ILit 1) 
                     
          plusOne :: FloatExpr -> FloatExpr 
          plusOne f = FBinOp OpAdd f (ILit 1)

          inductionStart :: NodePtr -> Maybe FloatExpr
          inductionStart def 
              = case getNodeInstOO def pGraph of 
                  Just (Store _ _ (Lit _ i))
                      | S.member (nodeLabel def) headerDomins -> Just $ ILit i 
                  Just (Store _ _ (Var _ v))
                      | S.member (nodeLabel def) headerDomins -> Just $ FVar v 
                  _ -> Nothing 
                                      
          -- Induction step attempts to tell us both what the step value of this induction variable is
          -- and whether the induction step is at the beginning or end of the loop (affects the "start" 
          -- value of the variable
          inductionStep :: Web -> NodePtr -> Maybe (Int64, InductionLoc) 
          inductionStep web def 
              = case inst of 
                  Just (Store _ v (BinOp _ OpAdd (Var _ x) (Lit _ i)))
                      | v == x -> indLoc i 
                  Just (Store _ v (BinOp _ OpSub (Var _ x) (Lit _ i)))
                      | v == x -> indLoc (-i)
                  Just (Store _ v (BinOp _ OpAdd (Lit _ i) (Var _ x))) 
                      | v == x -> indLoc i 
                  Just (Store _ v (BinOp _ OpAdd (UnOp _ OpNeg (Lit _ i)) (Var _ x)))
                      | v == x -> indLoc (-i)
                  _ -> Nothing

                where inst :: Maybe (MidIRInst O O)
                      inst = getNodeInstOO def pGraph
                      indLoc :: Int64 -> Maybe (Int64, InductionLoc)
                      indLoc i = case inductionLoc of 
                                   Nothing -> Nothing 
                                   Just loc -> Just (i, loc) 
                      inductionLoc
                          | beginningOfLoop def web = Just Beginning 
                          | endOfLoop def web = Just End 
                          | otherwise = Nothing

          beginningOfLoop :: NodePtr -> Web -> Bool 
          beginningOfLoop def web 
              = all (\use -> dominatesNode domins def use ) loopUses
                where loopUses = S.toList $ S.filter (\use -> S.member (nodeLabel use) body) $ webUses web 

          endOfLoop :: NodePtr -> Web -> Bool 
          endOfLoop def web 
              = (S.member (nodeLabel def) backDomins) && all loopUseOkay loopUses 
                where loopUses = S.toList $ S.filter (\u -> S.member (nodeLabel u) body) $ webUses web
                      loopUseOkay use
                          | use == def = True 
                          | dominatesNode domins use def = True 
                          | dominatesNode domins def use = False 
                          | S.member (nodeLabel use) reaches = False 
                          | otherwise = False
                      reaches = findReaching loopBack (nodeLabel def) pGraph mlabels 


          -- Makes the base variable, given a limit variable. 
          -- returns the limit variable if it is a base variable already
          makeBaseVar :: IndVar -> IndVar 
          makeBaseVar v@(_, ILit 0, _, 1) = v 
          makeBaseVar (v, init, end, inc) = (MV $ (show v) ++ "_base", ILit 0, iEnd, 1) 
              where iEnd
                        | inc == 1 = FBinOp OpSub end init
                        | otherwise = FBinOp OpMul (FLit incInv) (FBinOp OpSub end init)
                    incInv :: Double 
                    incInv = 1 / (fromIntegral inc) 


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
analyzeParallelizationPass midir = trace (show inductionVars) parallelLoops
    where loops = findLoops domins graph mlabels
          -- Let's see if we can identify induction vars
          sillyLoops = findLoopsSilly domins graph mlabels 
          inductionVars = S.map (\(Loop header body _, back) -> findInductionVariables pGraph mlabels domins webs (header, back, body)) sillyLoops 
          
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
                                       (Just linExpr1, Just linExpr2) -> noLinSoln loop linExpr1 linExpr2 
          
          -- Tests for whether two separate iterations of a given loop 
          -- can access the same data. Uses the glpk-hs package to solve 
          -- an integer linear program. 

          -- Given two expressions f(i, j) and g(i, j) for loop i. 
          -- have equations:
          -- f(i1, j1) = f(i2, j2) 
          -- i1 /= i2 (i1 <= i2-1 or i1 >= i2+1)
          -- i1, i2 >= imin and i1, i2 <= imax-1 
          -- j1, j2 >= jmin and j1, j2 <= jmax-1
          noLinSoln :: Loop -> MidIRExpr -> MidIRExpr -> Bool 
          noLinSoln loop expr1 expr2 
              = concreteBounds && noLessSoln && noGreaterSoln
              where noLessSoln = case unsafePerformIO $ LP.evalLPT lessLP of 
                                   Success -> False
                                   v -> True
                    noGreaterSoln = case unsafePerformIO $ LP.evalLPT greaterLP of 
                                      Success -> False 
                                      v -> True
                    concreteBounds = isJust bounds
                    loopVarInfo = Map.union myVariables $ Map.union parentVars childVars 
                    parentVars = Map.fromList [(n, i) | p <- loopParents Map.! loop, i@(n, _, _, _) <- loop_variables p]
                    childVars = Map.fromList [(n, i) | c <- loopChildren Map.! loop, i@(n, _, _, _) <- loop_variables c]
                    myVariables = Map.fromList [(n, i) | i@(n, _, _, _) <- loop_variables loop]

                    usedVariables :: S.Set VarName
                    usedVariables = S.union (fold_EE addUsedVariables S.empty expr1) (fold_EE addUsedVariables S.empty expr2)
                    addUsedVariables :: S.Set VarName -> MidIRExpr -> S.Set VarName 
                    addUsedVariables set (Var _ v) = S.insert v set 
                    addUsedVariables set _ = set

                    bounds :: Maybe (Map.Map VarName (Int64, Int64))
                    bounds = foldM maybeAddBounds Map.empty $ S.toList usedVariables
                    maybeAddBounds :: (Map.Map VarName (Int64, Int64)) -> VarName -> Maybe (Map.Map VarName (Int64, Int64))
                    maybeAddBounds map var 
                        = case Map.lookup var loopVarInfo of 
                            Just (_, (Lit _ l), (Lit _ u), _) 
                                | l <= u -> Just $ Map.insert var (l, u) map
                                | otherwise -> Just $ Map.insert var (u, l) map
                            _ -> Nothing
                    
                    mBounds = fromJust bounds

                    officialBounds :: Map.Map String (Int64, Int64) 
                    officialBounds = Map.union expr1Bounds expr2Bounds 

                    -- When we're doing the inequalities, we have to keep track of whether the looping variables 
                    -- are linear functions of the iteration (base induction variable). therefore, if j = a*i+b 
                    -- and i1 < i2, j1 < j2 only if a is positive. If not, i1 < i2 => j1 > j2. 
                    officialLoopVars :: [(String, String, Bool)]
                    officialLoopVars = [( (show var) ++ "_1", (show var) ++ "_2", i > 0) | (var, _, _, i) <- loop_variables loop]
                    
                    expr1Bounds = Map.fromList [( (show var) ++ "_1", mBounds Map.! var) | var <- S.toList usedVariables]
                    expr2Bounds = Map.fromList [( (show var) ++ "_2", mBounds Map.! var) | var <- S.toList usedVariables]

                    linFunc1 :: LinFunc String Int64
                    linFunc1 = fold_EE (addCoeffs "_1") Map.empty expr1 

                    linFunc2 :: LinFunc String Int64 
                    linFunc2 = fold_EE (addCoeffs "_2") Map.empty expr2

                    addCoeffs :: String -> LinFunc String Int64 -> MidIRExpr -> LinFunc String Int64
                    addCoeffs suf fun (BinOp _ OpAdd (Lit _ i) _) = addCoeff "parallel_const" i fun 
                    addCoeffs suf fun (BinOp _ OpAdd _ (Lit _ i)) = addCoeff "parallel_const" i fun 
                    addCoeffs suf fun (BinOp _ OpMul (Lit _ i) (Var _ v)) = addCoeff ( (show v) ++ suf) i fun
                    addCoeffs suf fun _ = fun

                    addCoeff :: String -> Int64 -> LinFunc String Int64 -> LinFunc String Int64 
                    addCoeff v i fun = case Map.lookup v fun of 
                                         Nothing -> Map.insert v i fun 
                                         Just i2 -> Map.insert v (i+i2) fun
                                                    
                    createMin1 :: String -> LinFunc String Int64
                    createMin1 v = (var v) ^-^ (var "parallel_const")

                    createPlus1 :: String -> LinFunc String Int64
                    createPlus1 v = (var v) ^+^ (var "parallel_const") 

                    lessLP :: LP.LPT String Int64 IO ReturnCode 
                    lessLP = do LP.setObjective Map.empty
                                -- Make the dependencies equal
                                LP.equal linFunc1 linFunc2
                                -- Set bounds on all of our looping variables
                                mapM (\(v, (l, u)) -> LP.setVarBounds v $ Bound l (u-1)) $ Map.toList officialBounds
                                LP.varEq "parallel_const" 1 -- and the "constant" variable should always be 1
                                -- Make our main looping variables (the current loop) inequal 
                                -- Specifically for this LP, make it < 
                                mapM (\(v1, v2, p) -> if p 
                                                      then LP.leq (var v1) (createMin1 v2)
                                                      else LP.geq (var v1) (createPlus1 v2)) officialLoopVars
                                -- Set the kinds on all of our variables 
                                mapM (\v -> LP.setVarKind v IntVar) $ Map.keys officialBounds
                                LP.setVarKind "parallel_const" IntVar
                                -- Finally, try to solve the integer linear program 
                                (code, _) <- LP.glpSolve $ mipDefaults {msgLev=MsgOff}
                                return code

                    greaterLP :: LP.LPT String Int64 IO ReturnCode 
                    greaterLP = do LP.setObjective Map.empty
                                   -- Make the dependencies equal
                                   LP.equal linFunc1 linFunc2
                                   -- Set bounds on all of our looping variables
                                   mapM (\(v, (l, u)) -> LP.setVarBounds v $ Bound l (u-1)) $ Map.toList officialBounds
                                   LP.varEq "parallel_const" 1 -- and the "constant" variable should always be 1
                                   -- Make our main looping variables (the current loop) inequal 
                                   -- Specifically for this LP, make it > 
                                   mapM (\(v1, v2, p) -> if p 
                                                         then LP.geq (var v1) (createPlus1 v2)
                                                         else LP.leq (var v2) (createMin1 v2)) officialLoopVars
                                   -- Set the kinds on all of our variables 
                                   mapM (\v -> LP.setVarKind v IntVar) $ Map.keys officialBounds
                                   LP.setVarKind "parallel_const" IntVar
                                   -- Finally, try to solve the integer linear program 
                                   (code, _) <- LP.glpSolve $ mipDefaults {msgLev=MsgOff} 
                                   return code


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
                                        False -> do newExpr <- makeLinear newExpr 
                                                    rejectNonLinear newExpr
                                                    
              where v@(variants, invariants) = loopVarInfos Map.! loop 
                    (variantNames, invariantNames) = loopVarNames v 
                    varNameToWebID :: Map.Map VarName WebID 
                    varNameToWebID = Map.fromList [(webVar $ getWeb id webs, id) | id <- S.toList $ S.union variants invariants]
                    availableLoopVars :: S.Set VarName 
                    availableLoopVars = S.union myVariables $ S.union parentVars childVars 
                    parentVars = S.fromList [var | p <- loopParents Map.! loop, (var, _, _, _) <- loop_variables p] 
                    childVars = S.fromList [var | c <- loopChildren Map.! loop, (var, _, _, _) <- loop_variables c]
                    myVariables = S.fromList [var | (var, _, _, _) <- loop_variables loop]

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
                    isNonLinear b (BinOp _ OpMul (Lit _ _) (Var _ _)) = b || False
                    isNonLinear b (BinOp _ OpAdd _ _) = b || False 
                    isNonLinear b (Lit _ _) = b || False 
                    isNonLinear b (Var _ _) = b || False 
                    isNonLinear b _ = True 

                    makeLinear :: MidIRExpr -> Maybe MidIRExpr 
                    makeLinear expr = case lineared of 
                                        Nothing -> Just expr 
                                        Just expr' -> makeLinear expr'
                        where lineared = mapEE linearize expr

                    linearize :: MidIRExpr -> Maybe MidIRExpr 
                    -- Coefficients should be distributed
                    linearize (BinOp _ OpMul expr (BinOp _ op expr1 expr2))
                        | op == OpAdd || op == OpSub 
                            = Just $ (BinOp dsp op (BinOp dsp OpMul expr expr1) (BinOp dsp OpMul expr expr2))
                    -- Coefficients should be combined if they're multiplied
                    linearize (BinOp _ OpMul (Lit _ i1) (Lit _ i2)) = Just (Lit dsp (i1*i2))
                    linearize (BinOp _ OpMul expr (Lit _ i)) = Just $ BinOp dsp OpMul (Lit dsp i) expr
                    linearize (BinOp _ OpMul (Lit _ i1) (BinOp _ OpMul (Lit _ i2) expr)) 
                        = Just (BinOp dsp OpMul (Lit dsp (i1*i2)) expr)
                    linearize (BinOp _ OpSub expr1 expr2) = Just (BinOp dsp OpAdd expr1 (UnOp dsp OpNeg expr2))
                    linearize (UnOp _ OpNeg (Lit _ i)) = Just (Lit dsp (-i))
                    linearize (UnOp _ OpNeg (BinOp _ op expr1 expr2))
                        | op == OpAdd || op == OpSub 
                            = Just $ (BinOp dsp op (UnOp dsp OpNeg expr1) (UnOp dsp OpNeg expr2))
                    linearize (UnOp _ OpNeg (BinOp _ OpMul (Lit _ i) expr) ) 
                        =  Just $ BinOp dsp OpMul (Lit dsp (-i)) expr
                    linearize (UnOp _ OpNeg (UnOp _ OpNeg expr)) = Just expr
                    linearize (BinOp _ OpAdd (Lit _ i1) (Lit _ i2)) = Just (Lit dsp (i1+i2))
                    linearize _ = Nothing
                              


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
 
