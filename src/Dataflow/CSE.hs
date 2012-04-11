{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}
module Dataflow.CSE where 

import Dataflow.OptSupport
import Compiler.Hoopl
import IR
import qualified Data.Map as Map
import qualified Data.Set as S


type ExprFact = WithBot (Map.Map MidIRExpr VarName)
exprLattice :: DataflowLattice ExprFact 
exprLattice = DataflowLattice { fact_name = "Global CSE Lattice"
                              , fact_bot = Bot
                              , fact_join = intersectMaps }
    where intersectMaps :: Label -> OldFact ExprFact -> NewFact ExprFact -> (ChangeFlag, ExprFact)
          intersectMaps _ (OldFact old) (NewFact new) 
              = case (old, new) of 
                  (old', Bot) -> (NoChange, old') 
                  (Bot, new') -> (SomeChange, new') 
                  (PElem oldMap, PElem newMap) -> (ch, PElem j)
                      where j = Map.mapMaybeWithKey f oldMap
                            f k v = case Map.lookup k newMap of 
                                      Just v' -> if v == v' 
                                                 then Just v 
                                                 else Nothing
                                      Nothing -> Nothing 
                            ch = changeIf (Map.size j /= Map.size oldMap)

emptyExprFact :: ExprFact 
emptyExprFact = fact_bot exprLattice

exprAvailable :: S.Set VarName -> FwdTransfer MidIRInst ExprFact 
exprAvailable nonTemps = mkFTransfer ft 
    where
      ft :: MidIRInst e x -> ExprFact -> Fact x ExprFact 
      ft (Label _ _) f = f
      ft (PostEnter _ _) f = f
      ft (Enter _ _ args) f = foldl (flip invalidateExprsWith) f args
      ft (Store _ x expr) f = handleAssign x expr f
      ft (IndStore _ _ _) f = destroyLoads f
      ft (Call _ x _ _) f = invalidateExprsWith x f
      ft (Callout _ x _ _) f = invalidateExprsWith x f 
      ft (Branch _ l) f = mapSingleton l f
      ft (CondBranch _ _ tl fl) f 
          = mkFactBase exprLattice [ (tl, f) 
                                   , (fl, f) ]
      ft (Return _ _) f = mapEmpty 
      ft (Fail _) f = mapEmpty 
      handleAssign :: VarName -> MidIRExpr -> ExprFact -> ExprFact
      handleAssign x expr f = if isTemp nonTemps x 
                              then newFact 
                              else case expr of  
                                     (Var pos varName) 
                                         | isTemp nonTemps varName -> invalidateExprsWith x f
                                     _ -> f
          where newFact = PElem newMap 
                newMap = Map.insert expr x lastMap
                lastMap :: Map.Map MidIRExpr VarName
                lastMap = case f of
                            Bot -> Map.empty
                            PElem oldMap -> oldMap
      invalidateExprsWith :: VarName -> ExprFact -> ExprFact
      invalidateExprsWith _ Bot = Bot 
      invalidateExprsWith x (PElem oldMap) = PElem newMap 
          where newMap = Map.mapMaybeWithKey f oldMap 
                f k v = if containsVar x k
                        then Nothing
                        else Just v 
      destroyLoads :: ExprFact -> ExprFact 
      destroyLoads Bot = Bot 
      destroyLoads (PElem oldMap) = PElem newMap
          where newMap = Map.mapMaybeWithKey f oldMap
                f k v = if containsLoad k 
                        then Nothing
                        else Just v
-- Rewrite function: 

cseRewrite :: forall m. (FuelMonad m, UniqueNameMonad m) => S.Set VarName -> FwdRewrite m MidIRInst ExprFact 
cseRewrite nonTemps = deepFwdRw cse 
    where 
      cse :: MidIRInst e x -> ExprFact -> m (Maybe (Graph MidIRInst e x))
      cse (Store _ x (Var _ v)) f
          | isTemp nonTemps v = return Nothing 
      cse (Store pos x expr) f 
          | not $ isTemp nonTemps x
          = case lookupExpr expr f of 
              Just varName -> return $ Just $ insnToG $ Store pos x (Var pos varName)
              Nothing -> do tempName <- genUniqueName "cse"
                            let tempAssign = insnToG $ Store pos (MV tempName) expr
                                varAssign = insnToG $ Store pos x (Var pos (MV tempName)) 
                                newGraph = tempAssign <*> varAssign 
                            return $ Just newGraph
      cse _ f = return Nothing


lookupExpr :: MidIRExpr -> ExprFact -> Maybe VarName 
lookupExpr expr Bot = Nothing 
lookupExpr expr (PElem factMap) = Map.lookup expr factMap

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

isTemp :: S.Set VarName -> VarName -> Bool 
isTemp nonTemps v = not $ S.member v nonTemps