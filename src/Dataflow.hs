{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}
module Dataflow where 

import Dataflow.ConstProp
import Dataflow.DeadCode
import Dataflow.CSE
import Dataflow.BlockElim
import Dataflow.Flatten
import Dataflow.CopyProp
import Dataflow.Tailcall
import Dataflow.LICM
import Dataflow.Dominator
import Dataflow.OptSupport
--import Dataflow.NZP

import LoopAnalysis
import Parallelize

import Control.Monad
import Control.Monad.Trans

import Data.Int
import qualified Data.Set as S
import qualified Data.Map as Map
import Data.Maybe

import Compiler.Hoopl
import Compiler.Hoopl.Fuel
import IR
import Debug.Trace
import Data.Maybe
import CLI

import Dataflow.IRWebs

import DataflowTypes


--  liftFuel m = FM $ \f -> do { a <- m; return (a, f) }


---

data DFA = DFA
    { dfaOptCheck :: OptFlags -> Bool
    , dfaPerform :: MidIRRepr -> RM MidIRRepr }

individualAnalysis :: OptFlags -> DFA -> MidIRRepr -> RM MidIRRepr
individualAnalysis opts (DFA optCheck perform) midir
    = if optCheck opts then perform midir else return midir

dataflows :: [DFA]
dataflows
    = [ DFA optConstProp performConstPropPass
      -- , DFA optNZP performNZPPass
      , DFA optTailcall performTailcallPass
      , DFA optDeadCode performDeadCodePass
      , DFA optBlockElim performBlockElimPass
      , DFA (\opts -> optCommonSubElim opts || optFlat opts) performFlattenPass
      --, DFA optLICM performLICMPass
      , DFA optCommonSubElim performCSEPass
      , DFA optCopyProp performCopyPropPass
      -- doing constprop after flatten/cse does great good! see tests/codegen/fig18.6.dcf
      , DFA optConstProp performConstPropPass
      , DFA optDeadCode performDeadCodePass
      , DFA (\opts -> optCommonSubElim opts || optFlat opts || optUnflat opts ) performUnflattenPass 
      , DFA optCopyProp performCopyPropPass
      , DFA optConstProp performConstPropPass
      , DFA optDeadCode performDeadCodePass
      , DFA optTailcall performTailcallPass 
      --, DFA optParallelize performParallelizePass
      --, DFA optNZP performNZPPass
      , DFA optDeadCode performDeadCodePass 
      , DFA optBlockElim performBlockElimPass 
      -- It's good to end with this for good measure (and removes dead blocks)
      , DFA optDeadCode performDeadCodePass
      --, DFA optDeadCode testDominatorPass
      ]

performDataflowAnalysis :: OptFlags -> MidIRRepr -> RM MidIRRepr 
performDataflowAnalysis opts midir
    = foldl (>>=) (return midir) (map (individualAnalysis opts) dataflows)

performConstPropPass midir = performFwdPass constPropPass midir emptyFact
performCopyPropPass midir = performFwdPass copyPropPass midir emptyCopyFact
performDeadCodePass midir = performBwdPass deadCodePass midir S.empty
performBlockElimPass midir = performBwdPass blockElimPass midir Nothing
performFlattenPass midir = performFwdPass flattenPass midir ()
--performNZPPass midir = performFwdPass nzpPass midir emptyNZPFact
performTailcallPass midir = performBwdPass (tailcallPass midir) midir (fact_bot lastReturnLattice)

-- Type of analyzeAndRewrite*
type AnalyzeFun p a = (p RM MidIRInst a) -> MaybeC C [Label] -> Graph MidIRInst C C -> Fact C a -> RM (Graph MidIRInst C C, FactBase a, MaybeO C a)
performPass :: AnalyzeFun p a -> (p RM MidIRInst a) -> MidIRRepr -> a -> RM MidIRRepr
performPass analyzeAndRewrite pass midir eFact
  = do (graph', factBase, _) <- analyzeAndRewrite
                                pass
                                (JustC mlabels)
                                graph
                                (mapFromList (map (\l -> (l, eFact) ) mlabels))
       return $ midir { midIRGraph = graph' }
    where graph = midIRGraph midir
          mlabels = (map methodEntry $ midIRMethods midir)

performFwdPass :: (FwdPass RM MidIRInst a) -> MidIRRepr -> a -> RM MidIRRepr
performFwdPass = performPass analyzeAndRewriteFwd

performBwdPass :: (BwdPass RM MidIRInst a) -> MidIRRepr -> a -> RM MidIRRepr 
performBwdPass = performPass analyzeAndRewriteBwd

performCSEPass :: MidIRRepr -> RM MidIRRepr 
performCSEPass midir 
    = do nonTemps <- getVariables midir
         let nonTemps' = S.unions $ mapElems nonTemps
         performFwdPass (csePass nonTemps') midir emptyExprFact

performLICMPass midir = performBwdPass (licmPass loops) midir emptyMotionFact
    where loops = midirLoops midir

performUnflattenPass :: MidIRRepr -> RM MidIRRepr 
performUnflattenPass midir
    = do (_, factBase, _) <- analyzeAndRewriteBwd
                             liveAnalysisPass 
                             (JustC mlabels)
                             graph
                             (mapFromList (map (\l -> (l, S.empty)) mlabels))
         unFlatten factBase midir
    where graph = midIRGraph midir
          mlabels = (map methodEntry $ midIRMethods midir)

testDominatorPass :: MidIRRepr -> RM MidIRRepr 
testDominatorPass midir 
    = do (_, factBase, _) <- analyzeAndRewriteFwd
                             dominatorPass 
                             (JustC mlabels)
                             graph
                             (mapFromList (map (\l -> (l, fact_bot dominatorLattice) ) mlabels))
         let loops = findLoops factBase graph mlabels
             parallelLoops = analyzeParallelizationPass midir 
         return $ trace (show parallelLoops) midir 
    where graph = midIRGraph midir
          mlabels = (map methodEntry $ midIRMethods midir)

-- (trace (map (show . entryLabel) (forwardBlockList mlabels body)) body)

constPropPass :: (CheckpointMonad m, FuelMonad m) => FwdPass m MidIRInst ConstFact 
constPropPass = FwdPass 
                { fp_lattice = constLattice 
                , fp_transfer = varHasLit
                , fp_rewrite = constProp `thenFwdRw` simplify } 

--nzpPass :: (CheckpointMonad m, FuelMonad m) => FwdPass m MidIRInst NZPFact
--nzpPass = FwdPass
--          { fp_lattice = nzpLattice
--          , fp_transfer = varHasNZP
--          , fp_rewrite = nzpSimplify }


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

liveAnalysisPass :: (CheckpointMonad m, FuelMonad m) => BwdPass m MidIRInst Live 
liveAnalysisPass = BwdPass
                   { bp_lattice = liveLattice
                   , bp_transfer = liveness
                   , bp_rewrite = noBwdRewrite }

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

licmPass :: (CheckpointMonad m, FuelMonad m, UniqueNameMonad m)
            => S.Set Loop -> BwdPass m MidIRInst MotionFact
licmPass loops = trace (show loops) $ BwdPass
           { bp_lattice = motionLattice
           , bp_transfer = motionTransfer loops
           , bp_rewrite = motionRewrite loops }

dominatorPass :: (CheckpointMonad m, FuelMonad m, UniqueNameMonad m)
                 => FwdPass m MidIRInst DominFact
dominatorPass = FwdPass 
                { fp_lattice = dominatorLattice 
                , fp_transfer = dominatorAnalysis
                , fp_rewrite = noFwdRewrite }



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
            used (Parallel _ ll x _ el) f = S.insert x $ S.union (fact f el) (fact f ll)
            used (Branch _ l) f = fact f l
            used (ThreadReturn _ l) f = fact f l
            used (CondBranch _ _ tl fl) f = fact f tl `S.union` fact f fl
            used Return{} f = fact_bot getVarsLattice
            used Fail{} f = fact_bot getVarsLattice

            fact :: FactBase (S.Set VarName) -> Label -> S.Set VarName
            fact f l = fromMaybe S.empty $ lookupFact l f 


unFlatten :: FactBase Live -> MidIRRepr -> RM MidIRRepr 
unFlatten factbase (MidIRRepr fields strs meths graph)
    = do graph' <- mgraph'
         return $ MidIRRepr fields strs meths graph' 
    where GMany _ body _ = graph 
          mgraph' = do graphs' <- mapM (unFlattenBlock factbase) (mapElems body) 
                       return $ foldl (|*><*|) emptyClosedGraph graphs'

unFlattenBlock :: FactBase Live -> Block MidIRInst C C -> RM (Graph MidIRInst C C)
unFlattenBlock factbase block = if changed then do graphs' <- mapM (unFlattenBlock factbase) (mapElems body')
                                                   return $ foldl (|*><*|) emptyClosedGraph graphs'
                                else return $ graph'
    where graph' = mkFirst e <*> catGraphs inner' <*> fixedX 
          GMany _ body' _ = graph'
          (me, inner, mx) = blockToNodeList block 
          e :: MidIRInst C O
          x :: MidIRInst O C
          e = case me of 
                JustC e' -> e'
          x = case mx of 
                JustC x' -> x'
          (fixedX, xChanged) = replaceUnusedC x 
          innerAndChanged = map replaceUnused inner
          inner' = map fst innerAndChanged
          innerChanged = any snd innerAndChanged
          changed = innerChanged || xChanged
          usesMap = countUses (foldl countUses Map.empty inner) x
          exprMap = foldl mapExprs Map.empty inner 
          countUses :: Map.Map VarName Int -> MidIRInst e x -> Map.Map VarName Int 
          countUses oldUses inst = fold_EN (fold_EE incrementVar) oldUses inst 
          incrementVar :: Map.Map VarName Int -> MidIRExpr -> Map.Map VarName Int 
          incrementVar oldUses (Var _ v) = case Map.lookup v oldUses of 
                                             Just i -> Map.insert v (i+1) oldUses 
                                             Nothing -> Map.insert v 1 oldUses
          incrementVar oldUses _ = oldUses 
          
          -- FLAG: Should I be storing the divOp's here somehow?
          mapExprs :: Map.Map VarName MidIRExpr -> MidIRInst O O -> Map.Map VarName MidIRExpr 
          mapExprs oldMap (Store _ v expr) = Map.insert v expr oldMap 
          mapExprs oldMap _ = oldMap

          liveLater :: S.Set VarName 
          liveLater = S.unions $ successorLives 
          successorLives = catMaybes $ map (\l -> mapLookup l factbase) $ successors x 

          replaceUnused :: MidIRInst O O -> (Graph MidIRInst O O, Bool)
          replaceUnused inst = case (mapVN replaceVar) inst of 
                                 Nothing -> (mkMiddle inst, False)
                                 Just inst' -> (mkMiddle inst', True)

          replaceUnusedC :: MidIRInst O C -> (Graph MidIRInst O C, Bool) 
          replaceUnusedC inst = case (mapVN replaceVar) inst of 
                                  Nothing -> (mkLast inst, False)
                                  Just inst' -> (mkLast inst', True)

          replaceVar :: VarName -> Maybe MidIRExpr
          replaceVar v 
              | S.member v liveLater || (Map.lookup v usesMap) /= (Just 1) = Nothing 
          replaceVar v 
              =  Map.lookup v exprMap 
