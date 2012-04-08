{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.DeadCode where 

import qualified Data.Set as S

import Compiler.Hoopl 
import IR2
import Data.Maybe



type Live = S.Set VarName 
liveLattice :: DataflowLattice Live 
liveLattice = DataflowLattice { fact_name = "Live variables"
                              , fact_bot = S.empty 
                              , fact_join = add
                              } 
    where add _ (OldFact old) (NewFact new) = (ch, j)
              where  j = new `S.union` old
                     ch = changeIf (S.size j > S.size old) 

liveness :: BwdTransfer MidIRInst Live 
liveness = mkBTransfer live 
    where live :: MidIRInst e x -> Fact x Live -> Live
          live (Label _ _) f = f 
          live n@(Enter _ _ args) f = addUses (f S.\\ (S.fromList args)) n
          live n@(Store _ x _) f = addUses (S.delete x f) n 
          live n@(CondStore _ x _ _ _) f = addUses (S.delete x f) n 
          live n@(IndStore _ _ _) f = f
          live n@(Spill _ x) f = addUses f n 
          live n@(Reload _ x) f = addUses (S.delete x f) n 
          live n@(Call _ x _ _) f = addUses (S.delete x f) n
          live n@(Callout _ x _ _) f = addUses (S.delete x f) n 
          live n@(Branch _ l) f = addUses (fact f l) n 
          live n@(CondBranch _ _ tl fl) f = addUses (fact f tl `S.union` fact f fl) n 
          live n@(Return _ _) _ = addUses (fact_bot liveLattice) n 
          live n@(Fail _) _ = addUses (fact_bot liveLattice) n 

          fact :: FactBase Live -> Label -> Live 
          fact f l = fromMaybe S.empty $ lookupFact l f 

          addUses :: Live -> MidIRInst e x -> Live 
          addUses = fold_EN (fold_EE addVar) 
          addVar s (Var _ v) = S.insert v s 
          addVar s _ = s

deadAsstElim :: forall m . FuelMonad m => BwdRewrite m MidIRInst Live 
deadAsstElim = mkBRewrite d 
    where 
      d :: MidIRInst e x -> Fact x Live -> m (Maybe (Graph MidIRInst e x))
      d (Store _ x _) live 
          | not (x `S.member` live) = return $ Just emptyGraph
      d (CondStore _ x _ _ _) live 
          | not (x `S.member` live) = return $ Just emptyGraph
      d (Reload _ x) live 
          | not (x `S.member` live) = return $ Just emptyGraph
      d _ _  = return Nothing


fold_EE :: (a -> MidIRExpr -> a) -> a -> MidIRExpr -> a 
fold_EN :: (a -> MidIRExpr -> a) -> a -> MidIRInst e x -> a 

fold_EE f z e@(Lit _ _) = f z e 
fold_EE f z e@(Var _ _) = f z e
fold_EE f z e@(LitLabel _ _) = f z e 
fold_EE f z e@(Load _ expr) = f (f z expr) e 
fold_EE f z e@(UnOp _ _ expr) = f (f z expr) e
fold_EE f z e@(BinOp _ _ expr1 expr2) = f (f (f z expr2) expr1) e

fold_EN _ z (Label _ _) = z
fold_EN _ z (Enter _ _ _) = z
fold_EN f z (Store _ _ expr) = f z expr 
fold_EN f z (CondStore _ _ expr1 expr2 expr3) = f (f (f z expr3) expr2) expr1
fold_EN f z (IndStore _ expr1 expr2) = f (f z expr2) expr1
fold_EN _ z (Spill _ _) = z
fold_EN _ z (Reload _ _) = z
fold_EN f z (Call _ _ _ es) = foldl f z es 
fold_EN f z (Callout _ _ _ es) = foldl f z es 
fold_EN _ z (Branch _ _) = z
fold_EN f z (CondBranch _ expr _ _) = f z expr 
fold_EN _ z (Return _ Nothing) = z
fold_EN f z (Return _ (Just expr)) = f z expr
fold_EN _ z (Fail _) = z