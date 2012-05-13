{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.DeadCodeAsm(performDeadAsmPass, performDeadAsmPass') where 

import qualified Data.Set as S

import Dataflow.OptSupport
import Compiler.Hoopl 
import qualified IR as I
import Assembly
import AliveDead
import Data.Maybe
import Debug.Trace

performDeadAsmPass :: (CheckpointMonad m, FuelMonad m) => LowIRRepr -> m LowIRRepr
performDeadAsmPass asm
    = do graph' <- performDeadAsmPass' mlabels graph
         return $ asm { lowIRGraph = graph' }
      where graph = lowIRGraph asm
            mlabels = (map I.methodEntry $ lowIRMethods asm)

performDeadAsmPass' :: (CheckpointMonad m, FuelMonad m) => 
                       [Label] -> Graph Asm C C -> m (Graph Asm C C)
performDeadAsmPass' mlabels graph
    = do (graph', factBase, _) <- analyzeAndRewriteBwd
                                  deadAsmPass
                                  (JustC mlabels)
                                  graph
                                  (mapFromList (map (\l -> (l, fact_bot liveLattice)) mlabels))
         return graph'
                                                   
deadAsmPass :: (CheckpointMonad m, FuelMonad m) => BwdPass m Asm Live
deadAsmPass = BwdPass 
              { bp_lattice = liveLattice
              , bp_transfer = liveness
              , bp_rewrite = deadAsstElim }


type Live = (S.Set Reg, S.Set SpillLoc)

liveLattice :: DataflowLattice Live 
liveLattice = DataflowLattice { fact_name = "Live registers"
                              , fact_bot = (S.empty, S.empty)
                              , fact_join = joinProd add add
                              } 
    where add _ (OldFact old) (NewFact new) = (ch, j)
              where  j = new `S.union` old
                     ch = changeIf (S.size j > S.size old) 

liveness :: BwdTransfer Asm Live 
liveness = mkBTransfer3 livee livem livex
    where livee :: Asm C O -> Live -> Live
          livee n f = update f (getAliveDead n) ([], [])
          livem :: Asm O O -> Live -> Live
          livem n@(Spill _ r s) f = update f (getAliveDead n) ([], [s])
          livem n@(Reload _ s r) f = update f (getAliveDead n) ([s], [])
          livem n f = update f (getAliveDead n) ([], [])
          livex :: Asm O C -> FactBase Live -> Live
          livex n fs = update (joinOutFacts liveLattice n fs) (getAliveDead n) ([], [])
          
          fact :: FactBase Live -> Label -> Live 
          fact f l = fromMaybe (fact_bot liveLattice) $ lookupFact l f
          
          update :: Live -> AliveDead -> ([SpillLoc], [SpillLoc]) -> Live
          update (r, s) (alive, dead) (salive, sdead)
            = ( (r S.\\ S.fromList dead) `S.union` S.fromList alive
              , (s S.\\ S.fromList sdead) `S.union` S.fromList salive )


deadAsstElim :: forall m . FuelMonad m => BwdRewrite m Asm Live 
deadAsstElim = mkBRewrite d 
    where 
      d :: forall e x . Asm e x -> Fact x Live -> m (Maybe (Graph Asm e x))
      d (Spill pos r s) (live, slive) = if s `S.member` slive
                                        then return Nothing
                                        else return $ Just emptyGraph
      d n@(Reload{}) (live, slive) = handle n live
      d n@(MovIRMtoR _ (IRM_R rs) rd) f
          | rs == rd = return $ Just emptyGraph
      d n@(MovIRMtoR{}) (live, slive) = handle n live
      d n@(Mov64toR{}) (live, slive) = handle n live
      d n@(CMovRMtoR{}) (live, slive) = handle n live
      d n@(Lea{}) (live, slive) = handle n live
--      d n@(ALU_IRMtoR{}) live = handle n live -- need flags for this to work
      d _ _  = return Nothing

      handle :: Asm O O -> S.Set Reg -> m (Maybe (Graph Asm O O))
      handle n live = let (alive, dead) = getAliveDead n
                      in if S.null $ S.fromList dead `S.intersection` live
                         then return $ Just emptyGraph
                         else return Nothing
