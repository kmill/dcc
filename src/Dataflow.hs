{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}
module Dataflow where 

import Dataflow.ConstProp
import Dataflow.DeadCode
--import Dataflow.CSE
import Dataflow.BlockElim
import Dataflow.Flatten

import Control.Monad.Trans

import qualified Data.Set as S

import Compiler.Hoopl
import Compiler.Hoopl.Fuel
import IR2 
import Debug.Trace
import Data.Maybe

type RM = StupidFuelMonadT GM


instance UniqueNameMonad RM where
    genUniqueName = lift . genUniqueName

-- Silly Exercise

newtype StupidFuelMonadT m a = StupidFuelMonadT { runStupidFuelMonad :: Fuel -> m (Fuel, a) }

evalStupidFuelMonad :: Monad m => StupidFuelMonadT m a -> Fuel -> m a
evalStupidFuelMonad sfm fuel = do (_, r) <- runStupidFuelMonad sfm fuel
                                  return r


instance Monad m => Monad (StupidFuelMonadT m) where
    return x = StupidFuelMonadT (\fuel -> return (fuel, x))
    ma >>= f = StupidFuelMonadT (\fuel -> do (fuel', a) <- runStupidFuelMonad ma fuel
                                             runStupidFuelMonad (f a) fuel')

instance MonadTrans StupidFuelMonadT where
    lift ma = StupidFuelMonadT (\fuel -> do a <- ma 
                                            return (fuel, a) )

instance CheckpointMonad m => CheckpointMonad (StupidFuelMonadT m) where
    type Checkpoint (StupidFuelMonadT m) = (Fuel, Checkpoint m)
    checkpoint = StupidFuelMonadT (\fuel -> do cp <- checkpoint
                                               return (fuel, (fuel, cp)))
    restart (fuel, cp) = StupidFuelMonadT (\_ -> do restart cp 
                                                    return (fuel, ()))

instance Monad m => FuelMonad (StupidFuelMonadT m) where
    getFuel = StupidFuelMonadT (\fuel -> return (fuel, fuel))
    setFuel f = StupidFuelMonadT (\fuel -> return (f, ()))

instance FuelMonadT StupidFuelMonadT where
  runWithFuel fuel m = evalStupidFuelMonad m fuel
  liftFuel = lift
--  liftFuel m = FM $ \f -> do { a <- m; return (a, f) }


---

performDataflowAnalysis :: MidIRRepr -> RM MidIRRepr 
performDataflowAnalysis midir 
    = do midir <- performConstPropPass midir
         midir <- performDeadCodePass midir
         midir <- performBlockElimPass midir
--         midir <- performDeadCodePass midir
         midir <- performFlattenPass midir
         return midir

performConstPropPass :: MidIRRepr -> RM MidIRRepr 
performConstPropPass midir 
    = do (graph', factBase, _) <- analyzeAndRewriteFwd
                                  constPropPass
                                  (JustC mlabels)
                                  graph
                                  (mapFromList (map (\l -> (l, emptyFact) ) mlabels))
         return $ midir { midIRGraph = graph'}
    where graph = midIRGraph midir
          mlabels = (map methodEntry $ midIRMethods midir)

performFlattenPass :: MidIRRepr -> RM MidIRRepr 
performFlattenPass midir 
    = do (graph', factBase, _) <- analyzeAndRewriteFwd
                                  flattenPass
                                  (JustC mlabels)
                                  graph
                                  (mapFromList (map (\l -> (l,()) ) mlabels))
         return $ midir { midIRGraph = graph' }
    where graph = midIRGraph midir
          mlabels = (map methodEntry $ midIRMethods midir)


performDeadCodePass :: MidIRRepr -> RM MidIRRepr 
performDeadCodePass midir 
    = do (graph', factBase, _) <- analyzeAndRewriteBwd 
                                  deadCodePass
                                  (JustC mlabels)
                                  graph
                                  mapEmpty
         return $ midir { midIRGraph = graph' }
    where graph = midIRGraph midir 
          mlabels = (map methodEntry $ midIRMethods midir)

performBlockElimPass :: MidIRRepr -> RM MidIRRepr
performBlockElimPass midir
  = do (graph', factBase, _) <- analyzeAndRewriteBwd
                                blockElimPass
                                (JustC mlabels)
                                graph
                                mapEmpty
       return $ midir { midIRGraph = graph' }
    where graph = midIRGraph midir
          mlabels = (map methodEntry $ midIRMethods midir)

      
-- (trace (map (show . entryLabel) (forwardBlockList mlabels body)) body)

constPropPass :: (CheckpointMonad m, FuelMonad m) => FwdPass m MidIRInst ConstFact 
constPropPass = FwdPass 
                { fp_lattice = constLattice 
                , fp_transfer = varHasLit
                , fp_rewrite = constProp `thenFwdRw` simplify } 


deadCodePass :: (CheckpointMonad m, FuelMonad m) => BwdPass m MidIRInst Live
deadCodePass = BwdPass 
               { bp_lattice = liveLattice
               , bp_transfer = liveness
               , bp_rewrite = deadAsstElim }
               
blockElimPass :: (CheckpointMonad m, FuelMonad m) => BwdPass m MidIRInst LastLabel
blockElimPass = BwdPass
                { bp_lattice = lastLabelLattice
                , bp_transfer = lastLabelness
                , bp_rewrite = lastLabelElim }

flattenPass :: (CheckpointMonad m, FuelMonad m, UniqueNameMonad m)
               => FwdPass m MidIRInst ()
flattenPass = FwdPass
              { fp_lattice = nullLattice
              , fp_transfer = nullTransfer
              , fp_rewrite = flattenRewrite } 



---
--- Get used variables
---

getVariables :: MidIRRepr -> RM (FactBase (S.Set VarName))
getVariables midir 
    = do (_, factBase, _) <- analyzeAndRewriteBwd 
                             getVariablesPass
                             (JustC mlabels)
                             graph
                             mapEmpty
         return $ factBase
    where graph = midIRGraph midir 
          mlabels = (map methodEntry $ midIRMethods midir)


getVariablesPass :: (CheckpointMonad m, FuelMonad m)
                    => BwdPass m MidIRInst (S.Set VarName)
getVariablesPass = BwdPass
                   { bp_lattice = getVarsLattice
                   , bp_transfer = getVarsTransfer
                   , bp_rewrite = noBwdRewrite }
    where
      getVarsLattice :: DataflowLattice (S.Set VarName)
      getVarsLattice = DataflowLattice
                       { fact_name = "used variables"
                       , fact_bot = S.empty
                       , fact_join = add
                       }
          where add _ (OldFact old) (NewFact new) = (ch, j)
                    where j = new `S.union` old
                          ch = changeIf $ S.size j > S.size old

      getVarsTransfer :: BwdTransfer MidIRInst (S.Set VarName)
      getVarsTransfer = mkBTransfer used
          where
            used :: MidIRInst e x -> Fact x (S.Set VarName) -> S.Set VarName
            used Label{} f = f
            used (Enter _ _ args) f = f `S.union` (S.fromList args)
            used (Store _ x _) f = S.insert x f
            used IndStore{} f = f
            used (Call _ x _ _) f = S.insert x f
            used (Callout _ x _ _) f = S.insert x f
            used (Branch _ l) f = fact f l
            used (CondBranch _ _ tl fl) f = fact f tl `S.union` fact f fl
            used Return{} f = fact_bot getVarsLattice
            used Fail{} f = fact_bot getVarsLattice

            fact :: FactBase (S.Set VarName) -> Label -> S.Set VarName
            fact f l = fromMaybe S.empty $ lookupFact l f 
