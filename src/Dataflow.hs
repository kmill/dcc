{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}
module Dataflow where 

import Dataflow.ConstProp
import Dataflow.DeadCode
import Dataflow.CSE
import Dataflow.BlockElim
import Dataflow.Flatten
import Dataflow.CopyProp
import Dataflow.Tailcall
import Dataflow.NZP

import Control.Monad
import Control.Monad.Trans

import qualified Data.Set as S

import Compiler.Hoopl
import Compiler.Hoopl.Fuel
import IR
import Debug.Trace
import Data.Maybe
import CLI

type RM = StupidFuelMonadT GM

instance UniqueMonad RM where
    freshUnique = lift freshUnique

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


performDataflowAnalysis :: OptFlags -> MidIRRepr -> RM MidIRRepr 
performDataflowAnalysis opts midir = do 
  midir <- if optConstProp opts 
           then performConstPropPass midir 
           else return midir
  midir <- if optNZP opts
           then performNZPPass midir
           else return midir
  midir <- if optTailcall opts 
           then performTailcallPass midir 
           else return midir
  midir <- if optDeadCode opts 
           then performDeadCodePass midir 
           else return midir
  midir <- if optBlockElim opts
           then performBlockElimPass midir 
           else return midir
  midir <- if (optCommonSubElim opts || optFlat opts)
           then performFlattenPass midir 
           else return midir
  midir <- if optCommonSubElim opts
           then performCSEPass midir 
           else return midir
  midir <- if optCopyProp opts
           then performCopyPropPass midir 
           else return midir
  midir <- if optTailcall opts 
           then performTailcallPass midir 
           else return midir
  midir <- if optNZP opts
           then performNZPPass midir
           else return midir
  midir <- if optDeadCode opts
           then performDeadCodePass midir
           else return midir
  midir <- if optBlockElim opts
           then performBlockElimPass midir 
           else return midir
  return midir

performConstPropPass midir = performFwdPass constPropPass midir emptyFact
performCopyPropPass midir = performFwdPass copyPropPass midir emptyCopyFact
performDeadCodePass midir = performBwdPass deadCodePass midir S.empty
performBlockElimPass midir = performBwdPass blockElimPass midir Nothing
performFlattenPass midir = performFwdPass flattenPass midir ()
performNZPPass midir = performFwdPass nzpPass midir emptyNZPFact

performFwdPass :: (FwdPass (StupidFuelMonadT GM) MidIRInst a) -> MidIRRepr -> a -> RM MidIRRepr
performFwdPass pass midir eFact
  = do (graph', factBase, _) <- analyzeAndRewriteFwd
                                pass
                                (JustC mlabels)
                                graph
                                (mapFromList (map (\l -> (l, eFact) ) mlabels))
       return $ midir { midIRGraph = graph' }
    where graph = midIRGraph midir
          mlabels = (map methodEntry $ midIRMethods midir)

performBwdPass :: (BwdPass (StupidFuelMonadT GM) MidIRInst a) -> MidIRRepr -> a -> RM MidIRRepr 
performBwdPass pass midir eFact
    = do (graph', factBase, _) <- analyzeAndRewriteBwd 
                                  pass
                                  (JustC mlabels)
                                  graph
                                  (mapFromList (map (\l -> (l, eFact) ) mlabels))
         return $ midir { midIRGraph = graph' }
    where graph = midIRGraph midir 
          mlabels = (map methodEntry $ midIRMethods midir)

performCSEPass :: MidIRRepr -> RM MidIRRepr 
performCSEPass midir 
    = do nonTemps <- getVariables midir
         let nonTemps' = S.unions $ mapElems nonTemps
         (graph', factBase, _) <- analyzeAndRewriteFwd
                                  (csePass nonTemps')
                                  (JustC mlabels)
                                  graph
                                  (mapFromList (map (\l -> (l, emptyExprFact) ) mlabels))
         return $ midir { midIRGraph = graph'}
    where graph = midIRGraph midir 
          mlabels = (map methodEntry $ midIRMethods midir)

-- (trace (map (show . entryLabel) (forwardBlockList mlabels body)) body)

constPropPass :: (CheckpointMonad m, FuelMonad m) => FwdPass m MidIRInst ConstFact 
constPropPass = FwdPass 
                { fp_lattice = constLattice 
                , fp_transfer = varHasLit
                , fp_rewrite = constProp `thenFwdRw` simplify } 

nzpPass :: (CheckpointMonad m, FuelMonad m) => FwdPass m MidIRInst NZPFact
nzpPass = FwdPass
          { fp_lattice = nzpLattice
          , fp_transfer = varHasNZP
          , fp_rewrite = nzpSimplify }


copyPropPass :: (CheckpointMonad m, FuelMonad m) => FwdPass m MidIRInst CopyFact 
copyPropPass = FwdPass 
               { fp_lattice = copyLattice
               , fp_transfer = varIsCopy
               , fp_rewrite = copyProp }

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


csePass :: (CheckpointMonad m, FuelMonad m, UniqueNameMonad m) 
           => S.Set VarName -> FwdPass m MidIRInst ExprFact
csePass nonTemps = FwdPass 
                   { fp_lattice = exprLattice
                   , fp_transfer = exprAvailable nonTemps
                   , fp_rewrite = cseRewrite nonTemps }
                   
performTailcallPass :: MidIRRepr -> RM MidIRRepr
performTailcallPass midir
    = do graph' <- foldl (>>=) (return $ midIRGraph midir) (map forMethod (midIRMethods midir))
         return $ midir { midIRGraph = graph' }
    where forMethod :: Method -> Graph MidIRInst C C -> RM (Graph MidIRInst C C)
          forMethod (Method pos name entry postentry) graph
              = do (graph', _, _) <- analyzeAndRewriteBwd
                                     (tailcallPass name postentry argvars)
                                     (JustC mlabels)
                                     graph
                                     mapEmpty
                   return graph'
              where argvars = getVars (blockToNodeList (lookupLabel graph entry))
                    getVars :: (MaybeC C (MidIRInst C O), a, b) -> [VarName]
                    getVars (JustC (Enter _ _ args), _, _) = args
                    getVars _ = error "getVars: method label is not Enter! :-("
          mlabels = map methodEntry $ midIRMethods midir
          
          lookupLabel :: Graph MidIRInst C C -> Label -> Block MidIRInst C C
          lookupLabel (GMany _ g_blocks _) lbl = case mapLookup lbl g_blocks of
                                                   Just x -> x
                                                   Nothing -> error "ERROR"


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
            used PostEnter{} f = f
            used (Enter _ _ args) f = f `S.union` (S.fromList args)
            used (Store _ x _) f = S.insert x f
            used (DivStore _ x _ _ _) f = S.insert x f
            used IndStore{} f = f
            used (Call _ x _ _) f = S.insert x f
            used (Callout _ x _ _) f = S.insert x f
            used (Branch _ l) f = fact f l
            used (CondBranch _ _ tl fl) f = fact f tl `S.union` fact f fl
            used Return{} f = fact_bot getVarsLattice
            used Fail{} f = fact_bot getVarsLattice

            fact :: FactBase (S.Set VarName) -> Label -> S.Set VarName
            fact f l = fromMaybe S.empty $ lookupFact l f 
