{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}
module Dataflow.CSE where 

import Compiler.Hoopl
import IR2
import qualified Data.Map as Map
import qualified Data.Set as S


type ExprFact = WithBot (Map.Map MidIRExpr VarName)
exprLattice :: DataflowLattice ExprFact 
exprLattice = DataflowLattice { fact_name = "Global CSE Lattice"
                              , fact_bot = Bot
                              , fact_join = intersectMaps }
    where intersectMaps _ (OldFact old) (NewFact new) 
              = case (old, new) of 
                  (Bot, new') -> (SomeChange, new') 
                  (old', Bot) -> (NoChange, old') 
                  (PElem oldMap, PElem newMap) -> (ch, PElem j)
                      where j = Map.mapMaybeWithKey f oldMap
                            f k v = case Map.lookup k newMap of 
                                      Just v' -> if v == v' 
                                                 then Just v 
                                                 else Nothing
                                      Nothing -> Nothing 
                            ch = changeIf (Map.size j /= Map.size oldMap)



exprAvailable :: S.Set VarName -> FwdTransfer MidIRInst ExprFact 
exprAvailable nonTemps = mkFTransfer ft 
    where 
      ft :: MidIRInst e x -> ExprFact -> Fact x ExprFact 
      ft (Label _ _) f = f
      ft (Enter _ _ _) f = f
      ft (Store _ x expr) f = handleAssign x expr f
      ft (CondStore _ x _ _ _) f = invalidateExprsWith x f
      ft (IndStore _ _ _) f = destroyLoads f
      ft (Spill _ _) f = f
      ft (Reload _ _) f = f
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
                              else invalidateExprsWith x f 
          where newFact = PElem newMap 
                newMap = case f of 
                           Bot -> Map.insert expr x Map.empty 
                           PElem oldMap -> Map.insert expr x oldMap
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

containsLoad :: MidIRExpr -> Bool 
containsLoad (Load _ _) = True 
containsLoad (UnOp _ _ expr) = containsLoad expr
containsLoad (BinOp _ _ expr1 expr2) = (containsLoad expr1) || (containsLoad expr2)
containsLoad _ = False

containsVar :: VarName -> MidIRExpr -> Bool 
containsVar x (Var _ v) = x == v
containsVar x (Load _ expr) = containsVar x expr
containsVar x (UnOp _ _ expr) = containsVar x expr 
containsVar x (BinOp _ _ expr1 expr2) = (containsVar x expr1) || (containsVar x expr2) 
containsVar _ _ = False

isTemp :: S.Set VarName -> VarName -> Bool 
isTemp nonTemps v = not $ S.member v nonTemps