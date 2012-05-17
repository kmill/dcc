{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}
module Dataflow.CSE where 

import Dataflow.OptSupport
import Compiler.Hoopl
import IR
import qualified Data.Map as Map
import qualified Data.Set as S
import Debug.Trace

data CSEExprs = CSEUniv
              | CSEMap (Map.Map MidIRExpr VarName)
                deriving Show

type ExprFact = (S.Set VarName, CSEExprs)
exprLattice :: DataflowLattice ExprFact 
exprLattice = DataflowLattice { fact_name = "Global CSE Lattice"
                              , fact_bot = (S.empty, CSEUniv)
                              , fact_join = joinProd joinSets intersectMaps }
    where intersectMaps :: Label -> OldFact CSEExprs -> NewFact CSEExprs -> (ChangeFlag, CSEExprs)
          intersectMaps _ (OldFact old) (NewFact new) 
              = case (old, new) of 
                  (old', CSEUniv) -> (NoChange, old') 
                  (CSEUniv, new') -> (SomeChange, new') 
                  (CSEMap oldMap, CSEMap newMap) -> (ch, CSEMap j)
                      where j = Map.mapMaybeWithKey f oldMap
                            f k v = case Map.lookup k newMap of 
                                      Just v' -> if v == v' 
                                                 then Just v 
                                                 else Nothing
                                      Nothing -> Nothing 
                            ch = changeIf (Map.size j /= Map.size oldMap)

emptyExprFact :: ExprFact 
emptyExprFact = fact_bot exprLattice

setNonTemps :: S.Set VarName -> ExprFact -> ExprFact
setNonTemps nt (_, exprs) = (nt, exprs)

getNonTemps :: ExprFact -> S.Set VarName
getNonTemps (nt, _) = nt

exprAvailable :: FactBase (S.Set VarName) -> FwdTransfer MidIRInst ExprFact 
exprAvailable nonTemps = mkFTransfer ft 
    where
      ft :: MidIRInst e x -> ExprFact -> Fact x ExprFact 
      ft (Label _ _) f = f
      ft (PostEnter _ _) f = f
      ft (Enter _ l args) f = let nt = mapFindWithDefault S.empty l nonTemps
                              in (nt, CSEUniv)
      ft (Store _ x expr) f = handleAssign x expr f
      ft DivStore{} f = f -- assuming both expressions are variables!
      ft (IndStore _ _ _) f = destroyLoads f
      ft (Call _ x _ _) f = invalidateExprsWith x f
      ft (Callout _ x _ _) f = invalidateExprsWith x f 
      ft (Parallel _ ll _ _ el) f
          = mkFactBase exprLattice [ (ll, (S.empty, CSEUniv))
                                   , (el, f) ]
      ft (Branch _ l) f = mapSingleton l f
      ft (ThreadReturn _ l) f = mapSingleton l (S.empty, CSEUniv)
      ft (CondBranch _ _ tl fl) f 
          = mkFactBase exprLattice [ (tl, f) 
                                   , (fl, f) ]
      ft (Return _ _ _) f = mapEmpty 
      ft (Fail _) f = mapEmpty 
      handleAssign :: VarName -> MidIRExpr -> ExprFact -> ExprFact
      handleAssign x expr (nt, f)
        = if isTemp (nt, f) x 
          then (nt, newFact)
          else case expr of  
                 Var pos varName | isTemp (nt, f) varName -> invalidateExprsWith x (nt, f)
                 _ -> (nt, f)
          where newFact = CSEMap newMap 
                newMap = Map.insertWith (\old new -> old) expr x lastMap
                lastMap :: Map.Map MidIRExpr VarName
                lastMap = case f of
                            CSEUniv -> Map.empty
                            CSEMap oldMap -> oldMap
      invalidateExprsWith :: VarName -> ExprFact -> ExprFact
      invalidateExprsWith _ (nt, CSEUniv) = (nt, CSEUniv)
      invalidateExprsWith x (nt, (CSEMap oldMap)) = (nt, CSEMap newMap)
          where newMap = Map.mapMaybeWithKey f oldMap
                f k v = if containsVar x k
                        then Nothing
                        else Just v 
      destroyLoads :: ExprFact -> ExprFact 
      destroyLoads (nt, CSEUniv) = (nt, CSEUniv)
      destroyLoads (nt, (CSEMap oldMap)) = (nt, CSEMap newMap)
          where newMap = Map.mapMaybeWithKey f oldMap
                f k v = if containsLoad k 
                        then Nothing
                        else Just v
-- Rewrite function: 

cseRewrite :: forall m. (FuelMonad m, UniqueNameMonad m) =>
              FwdRewrite m MidIRInst ExprFact 
cseRewrite = deepFwdRw cse 
    where 
      cse :: MidIRInst e x -> ExprFact -> m (Maybe (Graph MidIRInst e x))
      cse (Store _ x (Var _ v)) f
          | isTemp f v = return Nothing 
      cse (Store pos x expr) f 
          | not $ isTemp f x
          = case lookupExpr expr f of 
              Just varName -> return $ Just $ insnToG $ Store pos x (Var pos varName)
              Nothing -> do tempName <- genUniqueName "cse"
                            let tempAssign = insnToG $ Store pos (MV tempName) expr
                                varAssign = insnToG $ Store pos x (Var pos (MV tempName)) 
                                newGraph = tempAssign <*> varAssign 
                            return $ Just newGraph
      cse _ f = return Nothing


lookupExpr :: MidIRExpr -> ExprFact -> Maybe VarName 
lookupExpr expr (_, CSEUniv) = Nothing 
lookupExpr expr (_, (CSEMap factMap)) = Map.lookup expr factMap

containsLoad :: MidIRExpr -> Bool 
containsLoad (Load _ _) = True 
containsLoad (UnOp _ _ expr) = containsLoad expr
containsLoad (BinOp _ _ expr1 expr2) = (containsLoad expr1) || (containsLoad expr2)
containsLoad (Cond _ expr1 expr2 expr3) = (containsLoad expr1) || (containsLoad expr2) || (containsLoad expr3)
containsLoad _ = False

containsVar :: VarName -> MidIRExpr -> Bool 
containsVar x (Var _ v) = x == v
containsVar x (Load _ expr) = containsVar x expr
containsVar x (UnOp _ _ expr) = containsVar x expr 
containsVar x (BinOp _ _ expr1 expr2) = (containsVar x expr1) || (containsVar x expr2) 
containsVar x (Cond _ expr1 expr2 expr3) = (containsVar x expr1) || (containsVar x expr2) || (containsVar x expr3)
containsVar _ _ = False

isTemp :: ExprFact -> VarName -> Bool 
isTemp (nonTemps, _) v = not $ S.member v nonTemps
