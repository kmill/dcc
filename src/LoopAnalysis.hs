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

-- The threshhold for when we think it's worth parallelizing a loop 
loopCostThreshold :: Double 
loopCostThreshold = 0

trace' a x = x

-- debug function for map find 
mFDebug :: (Ord k, Show k) => k -> Map.Map k v -> v 
mFDebug k map = case Map.lookup k map of 
                  Just v -> v
                  Nothing -> error $ "The problem was " ++ (show k)
                          

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

floorFloatExpr :: FloatExpr -> FloatExpr 
floorFloatExpr expr = case floored of 
                        Nothing -> expr 
                        Just expr' -> floorFloatExpr expr'
    where floored = mapFEE floorIt expr
          floorIt (FLit d) = Just $ ILit $ floor d
          floorIt _ = Nothing

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

makeLinear :: FloatExpr -> FloatExpr 
makeLinear expr = case lineared of 
                    Nothing -> expr 
                    Just expr' -> makeLinear expr'
    where lineared = mapFEE linearize expr

linearize :: FloatExpr -> Maybe FloatExpr
-- We're now in the land of floats 
linearize (ILit i) = Just $ FLit $ fromIntegral i
-- Coefficients should be distributed
linearize (FBinOp OpMul expr (FBinOp op expr1 expr2))
    | op == OpAdd || op == OpSub 
        = Just $ (FBinOp op (FBinOp OpMul expr expr1) (FBinOp OpMul expr expr2))
linearize (FBinOp OpMul (FBinOp op expr1 expr2) expr)
    | op == OpAdd || op == OpSub 
        = Just $ (FBinOp op (FBinOp OpMul expr expr1) (FBinOp OpMul expr expr2))
-- Coefficients should be combined if they're multiplied
linearize (FBinOp OpMul (FLit i1) (FLit i2)) = Just (FLit (i1*i2))
linearize (FUnOp OpNeg (FVar v)) = Just (FBinOp OpMul (FLit (-1)) (FVar v))
-- Or added or subtracted 
linearize (FBinOp OpMul expr (FLit i)) = Just $ FBinOp OpMul (FLit i) expr
linearize (FBinOp OpMul (FLit i1) (FBinOp OpMul (FLit i2) expr)) 
    = Just (FBinOp OpMul (FLit (i1*i2)) expr)
linearize (FBinOp OpSub expr1 expr2) = Just (FBinOp OpAdd expr1 (FUnOp OpNeg expr2))
linearize (FUnOp OpNeg (FLit i)) = Just (FLit (-i))
linearize (FUnOp OpNeg (FBinOp op expr1 expr2))
    | op == OpAdd || op == OpSub 
        = Just $ (FBinOp op (FUnOp OpNeg expr1) (FUnOp OpNeg expr2))
linearize (FUnOp OpNeg (FBinOp OpMul (FLit i) expr) ) 
    =  Just $ FBinOp OpMul (FLit (-i)) expr
linearize (FUnOp OpNeg (FUnOp OpNeg expr)) = Just expr
linearize (FBinOp OpAdd (FLit i1) (FLit i2)) = Just (FLit (i1+i2))
linearize _ = Nothing

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
                 , loop_variables :: S.Set IndVar
                 , loop_limit :: IndVar 
                 , loop_base :: IndVar }
            deriving (Eq, Ord, Show)

type BackEdge = (Label, Label)
type LoopVariable = (VarName, MidIRExpr, MidIRExpr, Int64)

type IndVar = (VarName, FloatExpr, FloatExpr, Int64) 

{-midirLoops :: MidIRRepr -> S.Set Loop
midirLoops midir = findLoops domins graph mlabels
    where graph = midIRGraph midir
          mlabels = map methodEntry $ midIRMethods midir
          domins = findDominators graph mlabels -}

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


findBasicLoops :: FactBase DominFact -> Graph MidIRInst C C -> [Label] -> S.Set BasicLoop 
findBasicLoops dominators graph mlabels = S.fromList loops
    where GMany _ body _ = graph
          backEdges = findBackEdges dominators (mapElems body)
          loops = map (backEdgeToLoop dominators graph mlabels) backEdges

findBackEdges :: NonLocal n => FactBase DominFact -> [Block n C C] -> [BackEdge]
findBackEdges _ [] = []
findBackEdges dominators (x:xs) = case mapLookup (entryLabel x) dominators of 
                                    Just (PElem domin) -> (maybeBackEdges domin) ++ (findBackEdges dominators xs)
                                    _ -> findBackEdges dominators xs
    where maybeBackEdges domin = [ (entryLabel x, y) | y <- successors x, S.member y domin]

backEdgeToLoop :: FactBase DominFact -> Graph MidIRInst C C -> [Label] -> BackEdge -> BasicLoop 
backEdgeToLoop dominators graph mlabels (loopBack, loopHeader) = (loopHeader, loopBack, loopBody) 
    where loopBody = S.insert loopHeader $ findReaching loopBack loopHeader graph mlabels
          headerDomins = case mapLookup loopHeader dominators of 
                           Just (PElem domin) -> domin
                           _ -> S.empty
         
type BasicLoop = (Label, Label, S.Set Label)
data InductionLoc = Beginning | End deriving (Eq, Show)

findInductionVariables :: Graph (PNode MidIRInst) C C -> [Label] -> FactBase DominFact -> Webs -> BasicLoop 
                       -> Maybe (IndVar, IndVar, S.Set IndVar)
findInductionVariables pGraph mlabels domins webs (header, loopBack, body)
    = case limitVar of 
        Nothing -> Nothing
        Just lv -> let bv = makeBaseVar lv 
                   in Just (lv, bv, makeRestOfTheVariables lv (makeBaseVar lv))
    where loopWebs = websIntersectingBlocks webs body 
          varNameToWebID = Map.fromList [(webVar $ getWeb id webs, id) | id <- S.toList loopWebs]
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
          makeReverseLimitVar _ 
              = Nothing

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
              = inductionInst web def inst
                where inst :: Maybe (MidIRInst O O)
                      inst = getNodeInstOO def pGraph
                      

          inductionInst :: Web -> NodePtr -> Maybe (MidIRInst O O) -> Maybe (Int64, InductionLoc)
          inductionInst web def inst
              = case inst of 
                  Just (Store _ v (BinOp _ OpAdd (Var _ x) (Lit _ i)))
                      | v == x -> indLoc i 
                  Just (Store _ v (BinOp _ OpSub (Var _ x) (Lit _ i)))
                      | v == x -> indLoc (-i)
                  Just (Store _ v (BinOp _ OpAdd (Lit _ i) (Var _ x))) 
                      | v == x -> indLoc i 
                  Just (Store _ v (BinOp _ OpAdd (UnOp _ OpNeg (Lit _ i)) (Var _ x)))
                      | v == x -> indLoc (-i)
                  Just (Store _ v (Var _ x)) -> do expr <- tryReplaceVar x 
                                                   let newInst = Just (Store dsp v expr)
                                                   inductionInst web def newInst 
                  _ -> Nothing 
                where indLoc :: Int64 -> Maybe (Int64, InductionLoc)
                      indLoc i = case inductionLoc of 
                                   Nothing -> Nothing 
                                   Just loc -> Just (i, loc) 
                      inductionLoc
                          | beginningOfLoop def web = Just Beginning 
                          | endOfLoop def web = Just End 
                          | otherwise = Nothing

          tryReplaceVar :: VarName -> Maybe MidIRExpr 
          tryReplaceVar v = let webID = varNameToWebID Map.! v 
                                web = getWeb webID webs
                                defs = webDefs web
                                singleDef = head $ S.toList defs 
                                replaceInst = getNodeInstOO singleDef pGraph 
                            in if S.size defs /= 1 
                               then Nothing 
                               else case replaceInst of 
                                      Just (Store _ _ new)
                                          -> Just new 
                                      _ -> Nothing

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
                          | (nodeLabel def) == loopBack && (nodeLabel use) /= loopBack = True 
                          | dominatesNode domins use def = True 
                          | dominatesNode domins def use = False 
                          | S.member (nodeLabel use) reaches = False 
                          | otherwise = False
                      reaches = findReaching loopBack (nodeLabel def) pGraph mlabels 


          -- Makes the base variable, given a limit variable. 
          -- returns the limit variable if it is a base variable already
          makeBaseVar :: IndVar -> IndVar 
          makeBaseVar v@(_, ILit 0, _, 1) = v 
          makeBaseVar (v, init, end, inc) = (MV $ "la_base_" ++ (show v) , ILit 0, iEnd, 1) 
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

calculateLoopCosts :: NonLocal n => Graph n C C -> S.Set BasicLoop -> S.Set Loop -> Map.Map Loop Double
calculateLoopCosts graph basicLoops loops = concreteLoopCosts
    where headerToBasicLoop = Map.fromList [(h, l) | l@(h, _, _) <- S.toList basicLoops]
          headerToConcreteLoop = Map.fromList [(loop_header l, l) | l <- S.toList loops] 

          concreteLoopCosts = Map.fromList [(l, headerToLoopCost Map.! loop_header l) | l <- S.toList loops]
          headerToLoopCost = Map.fromList [(h, findLoopCost l) | l@(h, _, _) <- S.toList basicLoops]
        

          looseChildren :: Map.Map BasicLoop (S.Set BasicLoop)
          looseChildren = Map.fromList [(l, findLoopChildren l) | l <- S.toList basicLoops]

          findLoopChildren :: BasicLoop -> S.Set BasicLoop
          findLoopChildren (ph, _, pb) = S.fromList [l | l <- S.toList basicLoops, isLoopChild l] 
              where isLoopChild (ch, _, cb)
                        = S.size cb < S.size pb && S.member ch pb 

          strictChildren :: Map.Map BasicLoop (S.Set BasicLoop) 
          strictChildren = Map.fromList [(l, findStrictChildren l) | l <- S.toList basicLoops]
          
          findStrictChildren :: BasicLoop -> S.Set BasicLoop 
          findStrictChildren parent = S.fromList [l | l <- S.toList children, isStrictChild l] 
              where children = fromMaybe S.empty $ Map.lookup parent looseChildren 
                    grandChildren = [fromMaybe S.empty $ Map.lookup c looseChildren | c <- S.toList children]
                    isStrictChild child = all (S.notMember child) grandChildren

          findLoopCost :: BasicLoop -> Double
          findLoopCost loop@(h, _, body) = iterations * (childCosts + blockCosts)
              where iterations = findNumIterations loop
                    childCosts = sum [findLoopCost c | c <- S.toList myStrictChilds]
                    myStrictChilds = fromMaybe S.empty $ Map.lookup loop strictChildren
                    myLooseChilds = fromMaybe S.empty $ Map.lookup loop looseChildren
                    allChildBlocks = S.unions $ S.toList $ S.map (\(_, _, b) -> b) myLooseChilds
                    blockCosts = sum [findBlockCost b | b <- S.toList body]
                    findBlockCost bLabel
                        | S.member bLabel allChildBlocks = 0 
                        | otherwise = let BodyBlock block = lookupBlock graph bLabel
                                          (_, inner, _) = blockToNodeList block
                                          in fromIntegral $ length inner

          defaultIterations = 50
          findNumIterations :: BasicLoop -> Double
          findNumIterations (h, _, b) 
              = case Map.lookup h headerToConcreteLoop of 
                  Nothing -> defaultIterations
                  Just loop -> let (_, _, end, _) = loop_base loop 
                               in case floorFloatExpr (makeLinear end) of 
                                    ILit i
                                          | (fromIntegral i) > defaultIterations -> fromIntegral i
                                    _ -> defaultIterations
                    

findIterationMap :: MidIRRepr -> Map.Map Label Int
findIterationMap midir = numIterations
    where basicLoops = findBasicLoops domins graph mlabels
          loops = S.fromList $ catMaybes [insertIndVars l | l <- S.toList basicLoops]
          graph = midIRGraph midir 
          pGraph = toPGraph graph 
          webs = getWebs mlabels pGraph
          mlabels = map methodEntry $ midIRMethods midir 
          domins = findDominators graph mlabels 

          iterationMap = Map.fromList [(l, findNumIterations l) | l <- S.toList basicLoops]
          showIterationMap = Map.fromList [(h, v) | ((h, _, _), v) <- Map.toList iterationMap]

          noParents = S.fromList [l | (l, p) <- Map.toList looseParents, S.null p]

          numIterations = S.fold findIterations Map.empty noParents 
          
          findIterations :: BasicLoop -> Map.Map Label Int -> Map.Map Label Int 
          findIterations l@(_, _, body) map = S.fold (addIterations n) newMap body 
              where newMap = S.fold findIterations map myChildren 
                    myChildren = fromMaybe S.empty $ Map.lookup l strictChildren
                    n = fromMaybe defaultIterations $ Map.lookup l iterationMap
                                   
                                            
          addIterations :: Int -> Label -> Map.Map Label Int -> Map.Map Label Int
          addIterations n label map = case Map.lookup label map of 
                                        Just i -> Map.insert label (i*n) map 
                                        Nothing -> Map.insert label n map 


          insertIndVars b@(header, back, body)
              = do (lv, bv, ivs) <- findInductionVariables pGraph mlabels domins webs b 
                   return $ Loop header body ivs lv bv

          headerToConcreteLoop = Map.fromList [(loop_header l, l) | l <- S.toList loops]

          looseParents :: Map.Map BasicLoop (S.Set BasicLoop)
          looseParents = Map.fromList [(l, findLoopParents l) | l <- S.toList basicLoops] 
          
          findLoopParents :: BasicLoop -> S.Set BasicLoop 
          findLoopParents (ch, _, cb) = S.fromList [l | l <- S.toList basicLoops, isLoopParent l]
              where isLoopParent (ph, _, pb) 
                        = S.size cb < S.size pb && S.member ch pb

          looseChildren = Map.fromList [(l, findLoopChildren l) | l <- S.toList basicLoops]

          findLoopChildren :: BasicLoop -> S.Set BasicLoop
          findLoopChildren (ph, _, pb) = S.fromList [l | l <- S.toList basicLoops, isLoopChild l] 
              where isLoopChild (ch, _, cb)
                        = S.size cb < S.size pb && S.member ch pb 

          strictChildren :: Map.Map BasicLoop (S.Set BasicLoop) 
          strictChildren = Map.fromList [(l, findStrictChildren l) | l <- S.toList basicLoops]
          
          findStrictChildren :: BasicLoop -> S.Set BasicLoop 
          findStrictChildren parent = S.fromList [l | l <- S.toList children, isStrictChild l] 
              where children = fromMaybe S.empty $ Map.lookup parent looseChildren 
                    grandChildren = [fromMaybe S.empty $ Map.lookup c looseChildren | c <- S.toList children]
                    isStrictChild child = all (S.notMember child) grandChildren


          defaultIterations = 10 
          findNumIterations :: BasicLoop -> Int 
          findNumIterations (h, _, b) 
              = case Map.lookup h headerToConcreteLoop of 
                  Nothing -> defaultIterations
                  Just loop -> let (_, _, firstEnd, _) = loop_base loop 
                                   end = FBinOp OpAdd (ILit 1) firstEnd
                               in case floorFloatExpr (makeLinear end) of 
                                    ILit i
                                          | (fromIntegral i) > defaultIterations -> (fromIntegral i)
                                    _ -> defaultIterations


analyzeParallelizationPass :: MidIRRepr -> S.Set Loop 
analyzeParallelizationPass midir = trace (show worthItCosts) worthIt
    where basicLoops = findBasicLoops domins graph mlabels
          -- Let's see if we can identify induction vars
          loops = S.fromList $ catMaybes [insertIndVars l | l <- S.toList basicLoops]
          loopCosts = calculateLoopCosts graph basicLoops loops
          worthItCosts = Map.fromList [(loop_header l, c) | (l, c) <- Map.toList loopCosts, S.member l worthIt]
          niceLoopCosts = Map.fromList [(loop_header l, v) | (l, v) <- Map.toList loopCosts]
          insertIndVars :: BasicLoop -> Maybe Loop 
          insertIndVars b@(header, back, body) 
              = do (lv, bv, ivs) <- findInductionVariables pGraph mlabels domins webs b 
                   return $ Loop header body ivs lv bv
                          
          
          -- First pass, removes obviously non-parallel loops (such as loops that contain returns or callouts)
          noBreaksRetsCallsLoops = S.filter (\l -> noCalls l && noRets l && noBreaks l) loops 
          -- Second pass, removes loops that write to values that aren't loop invariant (i.e. for loops calculating a sum)
          -- Actually, loops calculating a sum might still be parallelizable by induction variable identification. 
          noVariantWritesLoops = S.filter (\l -> noVariantWrites (loopVarInfos Map.! l) l) noBreaksRetsCallsLoops
          -- Third pass, removes all loops with cross-loop dependencies. This is the big one that involves solving some 
          -- equations. This should effectively return all of the parallelizable loops.
          parallelLoops = S.filter noCrossDependencies noVariantWritesLoops
          -- Finally, remove any loops that are children of other loops in the parallel group since we only want to parallelize
          -- the outer most loops 
          noChildren = S.filter notChild parallelLoops 
          notChild loop = all (\p -> S.notMember p parallelLoops) parents
              where parents = fromMaybe [] $ Map.lookup loop loopParents
          
          -- Only parallelize loops that meet a certain cost criteria
          worthIt = S.filter (\l -> fromMaybe 0 (Map.lookup l loopCosts) > loopCostThreshold) noChildren


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
          noCalls (Loop header body _ _ _) = all noCall $ S.toList body 
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
          noRets (Loop _ body _ _ _) = all noRet $ S.toList body 
              where noRet :: Label -> Bool 
                    noRet l = let BodyBlock block = lookupBlock graph l 
                                  (_, _, mx) = blockToNodeList block 
                                  in notARet mx 

          notARet :: MaybeC C (MidIRInst O C) -> Bool 
          notARet (JustC (Return _ _ _)) = False 
          notARet _ = True 
          
          noBreaks :: Loop -> Bool 
          noBreaks (Loop header body _ _ _) = all noBreak $ S.toList body  
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
              = case trace' ("HERE WITH: " ++ show (loop_header loop) ++ " EXPR1: " ++ show expr1 ++ " EXPR2: " ++ show expr2) $ (findLabel expr1, findLabel expr2) of 
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
          noLinSoln :: Loop -> FloatExpr -> FloatExpr -> Bool 
          noLinSoln loop expr1 expr2 
              = trace' ("HERE WITH " ++ show (loop_header loop) ++ " " ++ show glpkFailGT) $ concreteBounds && (noGreaterSoln || glpkFailGT) && (noLessSoln || glpkFailLT)
              where noLessSoln = case ltCode of 
                                   Success -> trace' ("SUCCESS " ++ show (loop_header loop)) False
                                   v -> trace' (show v) True
                    noGreaterSoln = case gtCode of 
                                      Success -> trace' ("SUCCESS " ++ show (loop_header loop)) False 
                                      v -> trace' (show v) True
                    (ltCode, maybeLTSolution) = unsafePerformIO $ LP.evalLPT lessLP 
                    (gtCode, maybeGTSolution) = unsafePerformIO $ LP.evalLPT greaterLP


                    glpkFailLT = case maybeLTSolution of 
                                   Just (_, solution) -> (solution Map.! "parallel_const") /= 1
                                   Nothing -> False 

                    glpkFailGT = case maybeGTSolution of 
                                   Just (_, solution) -> (solution Map.! "parallel_const") /= 1
                                   Nothing -> False

                    concreteBounds = isJust bounds && isJust indConstraints
                    loopVarInfo = Map.union myVariables $ Map.union parentVars childVars 
                    parentVars =  Map.fromList [(n, (i, p)) | p <- loopParents Map.! loop, i@(n, _, _, _) <- S.toList $ loop_variables p]
                    childVars = Map.fromList [(n, (i, c)) | c <- (mFDebug loop loopChildren), i@(n, _, _, _) <- S.toList $ loop_variables c]
                    myVariables = Map.fromList [(n, (i, loop)) | i@(n, _, _, _) <- S.toList $ loop_variables loop]

                    usedVariables :: S.Set VarName
                    usedVariables = S.insert base_loop_var $ S.union (fold_FEE addUsedVariables S.empty expr1) (fold_FEE addUsedVariables S.empty expr2)
                    addUsedVariables :: S.Set VarName -> FloatExpr -> S.Set VarName 
                    addUsedVariables set (FVar v) = S.insert v set 
                    addUsedVariables set _ = set

                    bounds :: Maybe (Map.Map VarName (FloatExpr, FloatExpr))
                    bounds = foldM maybeAddBounds Map.empty $ S.toList usedVariables
                    maybeAddBounds :: (Map.Map VarName (FloatExpr, FloatExpr)) -> VarName -> Maybe (Map.Map VarName (FloatExpr, FloatExpr))
                    maybeAddBounds map var 
                        = do ((_, init, end, inc), myLoop) <- Map.lookup var loopVarInfo
                             initExpr <- linConstFloatExpr myLoop init
                             endExpr <- linConstFloatExpr myLoop end
                             case inc > 0 of 
                               True -> return $ Map.insert var (initExpr, endExpr) map 
                               False -> return $ Map.insert var (endExpr, initExpr) map 
                    
                    mBounds = fromJust bounds

                    officialBounds :: Map.Map String (LinFunc String Double, LinFunc String Double) 
                    officialBounds = Map.union expr1Bounds expr2Bounds 
                    
                    (base_loop_var, _, _, _) = loop_base loop
                    base_1 = (show base_loop_var) ++ "_1"
                    base_2 = (show base_loop_var) ++ "_2"
                    
                    expr1Bounds = Map.fromList [( (show k) ++ "_1", makeLinFuncs "_1" v) | (k, v) <- Map.toList mBounds]
                    expr2Bounds = Map.fromList [( (show k) ++ "_2", makeLinFuncs "_2" v) | (k, v) <- Map.toList mBounds]
                    
                    makeLinFuncs suf (f1, f2) = (makeLinFunc suf f1, makeLinFunc suf f2)

                    -- Now need to create the constraints on all of the non-base variables 
                    -- So they're all a linear function of i
                    indConstraints :: Maybe (Map.Map VarName FloatExpr)
                    indConstraints = foldM maybeAddConstraint Map.empty $ S.toList usedVariables

                    maybeAddConstraint map var 
                        | var == myLoopVar = Just map
                        | otherwise = do correct <- linConstFloatExpr myLoop myConstraint
                                         return $ Map.insert var correct map
                        where ((_, init, end, inc), myLoop) = fromMaybe (error ":-{") $ Map.lookup var loopVarInfo 
                              (myLoopVar, _, _, _) = loop_base myLoop 
                              dInc = fromIntegral inc 
                              myConstraint = FBinOp OpAdd (FBinOp OpMul (FLit dInc) (FVar myLoopVar)) init

                    mCon = fromJust indConstraints
                                  

                    officialConstraints = Map.union expr1Con expr2Con
                    expr1Con = Map.fromList [( (show k) ++ "_1", makeLinFunc "_1" v) | (k, v) <- Map.toList mCon]
                    expr2Con = Map.fromList [( (show k) ++ "_2", makeLinFunc "_2" v) | (k, v) <- Map.toList mCon]

                    linFunc1 :: LinFunc String Double
                    linFunc1 = makeLinFunc "_1" expr1

                    linFunc2 :: LinFunc String Double 
                    linFunc2 = makeLinFunc "_2" expr2

                    makeLinFunc :: String -> FloatExpr -> LinFunc String Double 
                    makeLinFunc suf (FVar v) = var $ ((show v) ++ suf) 
                    makeLinFunc suf (FLit i) = Map.singleton "parallel_const" i
                    makeLinFunc suf expr = fold_FEE (addCoeffs suf) Map.empty expr

                    addCoeffs :: String -> LinFunc String Double -> FloatExpr -> LinFunc String Double
                    addCoeffs suf fun (FBinOp OpAdd (FLit i) _) = addCoeff "parallel_const" i fun 
                    addCoeffs suf fun (FBinOp OpAdd _ (FLit i)) = addCoeff "parallel_const" i fun 
                    addCoeffs suf fun (FBinOp OpAdd (FLit i) (FVar v)) = addCoeff ( (show v) ++ suf) 1 $ addCoeff "parallel_const" i fun
                    addCoeffs suf fun (FBinOp OpMul (FLit i) (FVar v)) = addCoeff ( (show v) ++ suf) i fun
                    --addCoeffs suf fun (FLit i) = addCoeff "parallel_const" i fun 
                    --addCoeffs suf fun (FVar v) = addCoeff ((show v) ++ suf) 1 fun
                    addCoeffs suf fun _ = fun

                    addCoeff :: String -> Double -> LinFunc String Double -> LinFunc String Double
                    addCoeff v i fun = case Map.lookup v fun of 
                                         Nothing -> Map.insert v i fun 
                                         Just i2 -> Map.insert v (i+i2) fun
                                                    
                    createMin1 :: String -> LinFunc String Double
                    createMin1 v = (var v) ^-^ (var "parallel_const")

                    createPlus1 :: String -> LinFunc String Double
                    createPlus1 v = (var v) ^+^ (var "parallel_const") 

                    testLP :: LP.LPM String Double ()
                    testLP =  do LP.setObjective Map.empty
                                -- Make the dependencies equal
                                 LP.equal linFunc1 linFunc2
                                -- Set bounds on all of our looping variables
                                 mapM (\(v, (l, u)) -> do LP.geq (var v) l 
                                                          LP.leq (var v) u) $ Map.toList officialBounds
                                -- Add the constraints to all of our looping variables
                                 mapM (\(v, c) -> LP.equal (var v) c) $ Map.toList officialConstraints
                                 LP.varEq "parallel_const" 1 -- and the "constant" variable should always be 1
                                -- Make our main looping variables (the current loop) inequal 
                                -- Specifically for this LP, make it < 
                                 LP.leq (var base_1) $ createMin1 base_2

                                -- Set the kinds on all of our variables 
                                 mapM (\v -> LP.setVarKind v IntVar) $ Map.keys officialBounds
                                 LP.setVarKind "parallel_const" IntVar
                                -- Finally, try to solve the integer linear program 

                    lessLP :: LP.LPT String Double IO (ReturnCode, Maybe (Double, Map.Map String Double)) 
                    lessLP = do LP.setObjective $ Map.singleton "parallel_const" 1
                                -- Make the dependencies equal
                                LP.equal linFunc1 linFunc2
                                -- Set bounds on all of our looping variables
                                mapM (\(v, (l, u)) -> do LP.geq (var v) l 
                                                         LP.leq (var v) u) $ Map.toList officialBounds
                                -- Add the constraints to all of our looping variables
                                mapM (\(v, c) -> LP.equal (var v) c) $ Map.toList officialConstraints
                                LP.varEq "parallel_const" 1
                                --LP.varEq "parallel_const" 1 -- and the "constant" variable should always be 1
                                -- Make our main looping variables (the current loop) inequal 
                                -- Specifically for this LP, make it < 
                                LP.leq (var base_1) $ createMin1 base_2

                                -- Set the kinds on all of our variables 
                                mapM (\v -> LP.setVarKind v IntVar) $ Map.keys officialBounds
                                LP.setVarKind "parallel_const" BinVar
                                -- Finally, try to solve the integer linear program 
                                (code, solution) <- LP.glpSolve $ mipDefaults {msgLev=MsgOff}
                                trace' (show solution) $ return (code, solution)

                    greaterLP :: LP.LPT String Double IO (ReturnCode, Maybe (Double, Map.Map String Double)) 
                    greaterLP = do LP.setObjective Map.empty
                                   -- Make the dependencies equal
                                   LP.equal linFunc1 linFunc2
                                   -- Set bounds on all of our looping variables
                                   mapM (\(v, (l, u)) -> do LP.geq (var v) l 
                                                            LP.leq (var v) u) $ Map.toList officialBounds
                                   -- Add the constraints to all of our looping variables
                                   mapM (\(v, c) -> LP.equal (var v) c) $ Map.toList officialConstraints
                                   LP.varEq "parallel_const" 1 -- and the "constant" variable should always be 1
                                   -- Make our main looping variables (the current loop) inequal 
                                   -- Specifically for this LP, make it > 
                                   LP.geq (var base_1) $ createPlus1 base_2

                                   -- set the kinds on all of our variables 
                                   mapM (\v -> LP.setVarKind v IntVar) $ Map.keys officialBounds
                                   LP.setVarKind "parallel_const" IntVar
                                   -- Finally, try to solve the integer linear program 
                                   (code, solution) <- LP.glpSolve $ mipDefaults {msgLev=MsgOff}
                                   trace' (show solution) $ return (code, solution) 

          linConstExpr :: Loop -> MidIRExpr -> Maybe FloatExpr
          linConstExpr loop expr = maybeExpr
              where maybeExpr = do newExpr <- return $ eliminateLabels expr 
                                   newExpr <- exprToFloatExpr newExpr
                                   linConstFloatExpr loop newExpr
          eliminateLabels :: MidIRExpr -> MidIRExpr 
          eliminateLabels expr = fromMaybe expr $ (mapEE maybeEliminateLabel) expr 
          maybeEliminateLabel (BinOp _ _ (LitLabel _ _) expr) = Just expr 
          maybeEliminateLabel (BinOp _ _ expr (LitLabel _ _)) = Just expr 
          maybeEliminateLabel _ = Nothing

                

          -- Try to place the expression into linear constant form 
          -- where the expression represents a linear function of a number 
          -- of available loop induction variables. Returns Nothing if the 
          -- expression can't be placed in linear constant form
          linConstFloatExpr :: Loop -> FloatExpr -> Maybe FloatExpr 
          linConstFloatExpr loop expr = do newExpr <- rejectObviousProblems expr
                                           case hasNonLoopVariables newExpr of 
                                             True -> do newExpr <- tryRemoveNonLoops newExpr
                                                        linConstFloatExpr loop newExpr
                                             False -> do newExpr <- trace' (show (makeLinear newExpr)) $ return $ makeLinear newExpr 
                                                         rejectNonLinear newExpr
                                                    
              where v@(variants, invariants) = loopVarInfos Map.! loop
                    (variantNames, invariantNames) = loopVarNames v 
                    varNameToWebID :: Map.Map VarName WebID 
                    varNameToWebID = Map.fromList [(webVar $ getWeb id webs, id) | id <- S.toList $ S.union variants invariants]
                    availableLoopVars :: S.Set VarName 
                    availableLoopVars = S.union myVariables $ S.union parentVars childVars 
                    parentVars = S.fromList [var | p <- mFDebug loop loopParents, (var, _, _, _) <- S.toList $ loop_variables p] 
                    childVars = S.fromList [var | c <- mFDebug loop loopChildren, (var, _, _, _) <- S.toList $ loop_variables c]
                    myVariables = S.fromList [var | (var, _, _, _) <- S.toList $ loop_variables loop]

                    rejectObviousProblems :: FloatExpr -> Maybe FloatExpr 
                    rejectObviousProblems expr
                        | fold_FEE isObviousProblem False expr = Nothing 
                        | otherwise = Just expr

                    isObviousProblem :: Bool -> FloatExpr -> Bool 
                    isObviousProblem b (FVar v)
                        | S.member v variantNames && S.notMember v availableLoopVars = True
                    isObviousProblem b _ = b 

                    rejectNonLinear :: FloatExpr -> Maybe FloatExpr 
                    rejectNonLinear expr 
                        | fold_FEE isNonLinear False expr = Nothing 
                        | otherwise = Just expr 

                    isNonLinear :: Bool -> FloatExpr -> Bool 
                    isNonLinear b (FBinOp OpMul (FLit _) (FVar _)) = b || False
                    isNonLinear b (FBinOp OpAdd _ _) = b || False 
                    isNonLinear b (FLit _) = b || False 
                    isNonLinear b (FVar _) = b || False 
                    isNonLinear b _ = True 

                    hasNonLoopVariables :: FloatExpr -> Bool 
                    hasNonLoopVariables expr = fold_FEE isNonLoopVar False expr 
                    isNonLoopVar :: Bool -> FloatExpr -> Bool 
                    isNonLoopVar b (FVar v) 
                        | S.notMember v availableLoopVars = True 
                    isNonLoopVar b _ = b 

                    tryRemoveNonLoops :: FloatExpr -> Maybe FloatExpr 
                    tryRemoveNonLoops expr = foldM removeNonLoop expr $ S.toList nonLoopVars
                        where nonLoopVars = fold_FEE addNonLoopVars S.empty expr 
                              addNonLoopVars s (FVar v) 
                                  | S.notMember v availableLoopVars = S.insert v s 
                              addNonLoopVars s _ = s
                              removeNonLoop :: FloatExpr -> VarName -> Maybe FloatExpr 
                              removeNonLoop expr v
                                  = let webID = trace' ("REPLACE VAR " ++ show (loop_header loop) ++ " " ++ show expr) $ mFDebug v varNameToWebID 
                                        web = getWeb webID webs
                                        defs = webDefs web
                                        singleDef = head $ S.toList defs
                                        replaceInst = getNodeInstOO singleDef pGraph
                                    in if S.size defs /= 1 
                                       then Nothing 
                                       else case trace' (show replaceInst) replaceInst of 
                                              Just (Store _ _ new) 
                                                  -> case exprToFloatExpr new of 
                                                       Just fNew -> Just $ fromMaybe expr $ mapFEE (replaceVar v fNew) expr   
                                                       _ -> Nothing
                                              _ -> Nothing 

                              replaceVar :: VarName -> FloatExpr -> FloatExpr -> Maybe FloatExpr 
                              replaceVar v expr (FVar x) 
                                  | v == x = Just $ expr 
                              replaceVar _ _ _ = Nothing

          


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
              | not ( (webVar web) `elem` [x | (x, _, _, _) <- S.toList loopVars] ) = False
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
 
