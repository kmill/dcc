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
      ft (Store _ x expr) f = theThing 
      ft (CondStore _ x _ _ _) f = theThing 
      ft (IndStore _ _ _) f = destroyLoads
      ft (Spill _ _) f = destroyLoads
      ft (Reload _ _) f = theThing
      ft (Call _ _ _ _) f = theThing
      ft (Callout _ _ _ _) f = theThing 
      ft (Branch _ l) f = mapSingleton l f
      ft (CondBranch _ _ tl fl) f 
          = mkFactBase exprLattice [ (tl, f) 
                                   , (fl, f) ]
      ft (Return _ _) f = mapEmpty 
      ft (Fail _) f = mapEmpty 
      handleAssign :: VarName -> ExprFact -> ExprFact 
      destroyLoads :: ExprFact -> ExprFact 
      destroyLoads Bot = Bot 
      destroyLoads (PElem oldMap) = PElem newMap
          where newMap = Map.mapMaybeWithKey f oldMap
                f = 


isTemp :: S.Set VarName -> VarName 
isTemp nonTemps v = not $ member v nonTemps