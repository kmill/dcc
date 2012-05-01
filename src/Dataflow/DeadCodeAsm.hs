{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.DeadCodeAsm(performDeadAsmPass) where 

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
    = do (graph', factBase, _) <- analyzeAndRewriteBwd
                                  deadAsmPass
                                  (JustC mlabels)
                                  graph
                                  (mapFromList (map (\l -> (l, S.empty)) mlabels))
         return $ asm { lowIRGraph = graph' }
      where graph = lowIRGraph asm
            mlabels = (map I.methodEntry $ lowIRMethods asm)

                                                   
deadAsmPass :: (CheckpointMonad m, FuelMonad m) => BwdPass m Asm Live
deadAsmPass = BwdPass 
              { bp_lattice = liveLattice
              , bp_transfer = liveness
              , bp_rewrite = deadAsstElim }


type Live = S.Set Reg

liveLattice :: DataflowLattice Live 
liveLattice = DataflowLattice { fact_name = "Live registers"
                              , fact_bot = S.empty 
                              , fact_join = add
                              } 
    where add _ (OldFact old) (NewFact new) = (ch, j)
              where  j = new `S.union` old
                     ch = changeIf (S.size j > S.size old) 

liveness :: BwdTransfer Asm Live 
liveness = mkBTransfer3 livee livem livex
    where livee :: Asm C O -> Live -> Live
          livee n f = update f (getAliveDead n)
          livem :: Asm O O -> Live -> Live
          livem n f = update f (getAliveDead n)
          livex :: Asm O C -> FactBase Live -> Live
          livex n f = update (S.unions (map (fact f) $ successors n)) (getAliveDead n)
          
          fact :: FactBase Live -> Label -> Live 
          fact f l = fromMaybe S.empty $ lookupFact l f 
          
          update :: Live -> AliveDead -> Live
          update f (alive, dead) = (f S.\\ S.fromList dead) `S.union` S.fromList alive


deadAsstElim :: forall m . FuelMonad m => BwdRewrite m Asm Live 
deadAsstElim = mkBRewrite d 
    where 
      d :: forall e x . Asm e x -> Fact x Live -> m (Maybe (Graph Asm e x))
      d n@(Reload{}) live = handle n live
      d n@(MovIRMtoR{}) live = handle n live
      d n@(Mov64toR{}) live = handle n live
      d n@(CMovRMtoR{}) live = handle n live
      d n@(Lea{}) live = handle n live
--      d n@(ALU_IRMtoR{}) live = handle n live -- need flags for this to work
      d _ _  = return Nothing

      handle :: Asm O O -> Live -> m (Maybe (Graph Asm O O))
      handle n live = let (alive, dead) = getAliveDead n
                      in if S.null $ S.fromList dead `S.intersection` live
                         then return $ Just emptyGraph
                         else return Nothing
