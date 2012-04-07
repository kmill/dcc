{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies  #-}
module Dataflow where 

import Dataflow.ConstProp

import Control.Monad.Trans

import Compiler.Hoopl
import Compiler.Hoopl.Fuel
import IR2 
import Debug.Trace

type RM = CheckingFuelMonad GM




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

---

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

      
-- (trace (map (show . entryLabel) (forwardBlockList mlabels body)) body)

constPropPass :: (CheckpointMonad m, FuelMonad m) => FwdPass m MidIRInst ConstFact 
constPropPass = FwdPass 
                { fp_lattice = constLattice 
                , fp_transfer = varHasLit
                , fp_rewrite = constProp `thenFwdRw` simplify } 

