{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.DeadCode where 

import qualified Data.Set as S

import Dataflow.OptSupport
import Compiler.Hoopl 
import IR
import Data.Maybe
import Debug.Trace



type Live = S.Set VarName 
liveLattice :: DataflowLattice Live 
liveLattice = DataflowLattice { fact_name = "Live variables"
                              , fact_bot = S.empty 
                              , fact_join = add
                              } 
    where add _ (OldFact old) (NewFact new) = (ch, j)
              where  j = new `S.union` old
                     ch = changeIf (S.size j > S.size old) 

-- Old Liveness function 
{-liveness :: BwdTransfer MidIRInst Live 
liveness = mkBTransfer live 
    where live :: MidIRInst e x -> Fact x Live -> Live
          live (Label _ _) f = f 
          live (PostEnter _ _) f = f 
          live n@(Enter _ _ args) f = addUses (f S.\\ (S.fromList args)) n
          live n@(Store _ x _) f =  addUses (S.delete x f) n 
          live n@(DivStore _ x _ _ _) f =  addUses (S.delete x f) n 
          live n@(IndStore _ _ _) f = addUses f n 
          live n@(Call _ x _ _) f = addUses (S.delete x f) n
          live n@(Callout _ x _ _) f = addUses (S.delete x f) n 
          live n@(Branch _ l) f = addUses (fact f l) n 
          live n@(CondBranch _ _ tl fl) f = addUses (fact f tl `S.union` fact f fl) n 
          live n@(Return _ _ _) _ = addUses (fact_bot liveLattice) n 
          live n@(Fail _) _ = addUses (fact_bot liveLattice) n 

          fact :: FactBase Live -> Label -> Live 
          fact f l = fromMaybe S.empty $ lookupFact l f 

          addUses :: Live -> MidIRInst e x -> Live 
          addUses = fold_EN (fold_EE addVar) 
          addVar s (Var _ v) = S.insert v s 
          addVar s _ = s-}

liveness :: BwdTransfer MidIRInst Live 
liveness = mkBTransfer3 liveCO liveOO liveOC  
    where liveCO :: MidIRInst C O -> Live -> Live
          liveCO inst f = S.union (f S.\\ (S.fromList dead)) $ S.fromList alive
              where (alive, dead) = getMidAliveDead inst 

          liveOO :: MidIRInst O O -> Live -> Live 
          liveOO inst f = S.union (f S.\\ (S.fromList dead)) $ S.fromList alive 
              where (alive, dead) = getMidAliveDead inst 

          liveOC :: MidIRInst O C -> FactBase Live -> Live 
          liveOC inst@(Branch _ l) fb = S.union (f S.\\ (S.fromList dead)) $ S.fromList alive 
              where f = fact fb l 
                    (alive, dead) = getMidAliveDead inst 
          liveOC inst@(ThreadReturn _ l) fb = S.empty
          liveOC inst@(CondBranch _ _ tl fl) fb = S.union (f S.\\ (S.fromList dead)) $ S.fromList alive 
              where f = fact fb tl `S.union` fact fb fl
                    (alive, dead) = getMidAliveDead inst
          liveOC inst@(Parallel _ ll _ _ el) fb = S.union ((S.delete f var) S.\\ (S.fromList dead)) $ S.fromList alive 
              where f = fact fb ll `S.union` fact fb el
                    (alive, dead) = getMidAliveDead inst
          liveOC inst@(Return _ _ _) _ = S.fromList alive 
              where (alive, _) = getMidAliveDead inst 
          liveOC inst@(Fail _) _ = S.fromList alive 
              where (alive, _) = getMidAliveDead inst 

          fact :: FactBase Live -> Label -> Live 
          fact f l = fromMaybe S.empty $ lookupFact l f 


deadAsstElim :: forall m . FuelMonad m => BwdRewrite m MidIRInst Live 
deadAsstElim = mkBRewrite d 
    where 
      d :: MidIRInst e x -> Fact x Live -> m (Maybe (Graph MidIRInst e x))
      d n@(Store _ x _) live 
          | not (x `S.member` live) = return $ Just emptyGraph
      d n@(DivStore _ x _ _ (Lit _ i)) live 
          | i /= 0 && not (x `S.member` live) = return $ Just emptyGraph
      d _ _  = return Nothing

