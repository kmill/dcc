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
import Dataflow.CondElim
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

dataflows :: CompilerOpts -> [DFA]
dataflows copts
    = [ DFA optConstProp performConstPropPass
      -- , DFA optNZP performNZPPass
      , DFA optTailcall performTailcallPass
      , DFA optCondElim performCondElimPass
      , DFA optDeadCode performDeadCodePass
      , DFA optCondElim performCondElimPass
      , DFA optBlockElim performBlockElimPass

      , DFA optConstProp performConstPropPass        
      , DFA optFlat performFlattenPass
      --, DFA optLICM performLICMPass
      , DFA optCommonSubElim performCSEPass
      , DFA optCopyProp performCopyPropPass
      -- doing constprop after flatten/cse does great good! see tests/codegen/fig18.6.dcf
      , DFA optConstProp performConstPropPass
      , DFA optDeadCode performDeadCodePass
      , DFA optUnflat performUnflattenPass 
        
      , DFA optConstProp performConstPropPass
      , DFA optFlat performFlattenPass
      --, DFA optLICM performLICMPass
      , DFA optCommonSubElim performCSEPass
      , DFA optCopyProp performCopyPropPass
      -- doing constprop after flatten/cse does great good! see tests/codegen/fig18.6.dcf
      , DFA optConstProp performConstPropPass
      , DFA optDeadCode performDeadCodePass
      , DFA optUnflat performUnflattenPass 

        
      , DFA optCopyProp performCopyPropPass
      , DFA optConstProp performConstPropPass
      , DFA optDeadCode performDeadCodePass
      , DFA optTailcall performTailcallPass 
      , DFA optParallelize (performParallelizePass copts)
      , DFA optConstProp performConstPropPass
      , DFA optCopyProp performCopyPropPass
      --, DFA optNZP performNZPPass
      , DFA optDeadCode performDeadCodePass 
      , DFA optBlockElim performBlockElimPass 
      -- It's good to end with this for good measure (and removes dead blocks)
      , DFA optDeadCode performDeadCodePass
      --, DFA optDeadCode testDominatorPass
      , DFA (hasOptFlag "winnowstr") removeUnusedStrings
      ]
      
    where
      optCommonSubElim = hasOptFlag "cse"
      optCopyProp = hasOptFlag "copyprop"
      optConstProp opts = hasOptFlag "constprop" opts || optParallelize opts
      optCondElim = hasOptFlag "condelim"
      optNZP = hasOptFlag "nzp"
      optDeadCode = hasOptFlag "deadcode"
      optBlockElim = hasOptFlag "blockelim"
      optFlat opts = hasOptFlag "flat" opts
      optUnflat opts = hasOptFlag "unflat" opts
      optTailcall = hasOptFlag "tailcall"
      optLICM = hasOptFlag "licm"
      optParallelize = hasOptFlag "parallelize"
      optDeadCodeAsm = hasOptFlag "deadcodeasm"

performDataflowAnalysis :: CompilerOpts -> MidIRRepr -> RM MidIRRepr 
performDataflowAnalysis copts midir
    = foldl (>>=) (return midir)
      (map (individualAnalysis (optMode copts)) (dataflows copts))

performConstPropPass midir = performFwdPass constPropPass midir emptyFact
performCopyPropPass midir = performFwdPass copyPropPass midir emptyCopyFact
performDeadCodePass midir = performBwdPass deadCodePass midir S.empty
performCondElimPass midir = performBwdPass condElimPass midir emptyCEFact
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
         performFwdPass (csePass nonTemps) midir emptyExprFact
--         performFwdPass (pairFwd copyPropPass (csePass nonTemps')) midir (fact_bot copyLattice, emptyExprFact)

performLICMPass midir = performBwdPass (licmPass loops) midir emptyMotionFact
    where loops = error "Can't use midir loops to get loops anymore"

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
         let parallelLoops = analyzeParallelizationPass midir
             parallelHeaders = S.map (loop_header) parallelLoops
             iterations = findIterationMap midir
         return $ trace (show iterations) midir 
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

condElimPass :: (CheckpointMonad m, FuelMonad m) => BwdPass m MidIRInst AssignMap 
--condElimPass = debugBwdJoins trace (const True) $ BwdPass 
--condElimPass = debugBwdTransfers trace show (const $ const True) $ debugBwdJoins trace (const True) $ BwdPass 
condElimPass = BwdPass
                { bp_lattice = condAssignLattice
               , bp_transfer = condAssignness
               , bp_rewrite = condElim }

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
              { fp_lattice = noLattice
              , fp_transfer = noTransfer
              , fp_rewrite = flattenRewrite } 


csePass :: (CheckpointMonad m, FuelMonad m, UniqueNameMonad m) 
           => FactBase (S.Set VarName) -> FwdPass m MidIRInst ExprFact
csePass nonTemps = FwdPass 
                   { fp_lattice = exprLattice
                   , fp_transfer = exprAvailable nonTemps
                   , fp_rewrite = cseRewrite }

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
                   { bp_lattice = setLattice
                   , bp_transfer = getVarsTransfer
                   , bp_rewrite = noBwdRewrite }
    where
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
            used (Parallel _ l x _ l2) f = S.insert x $ fact f l `S.union` fact f l2
            used (Branch _ l) f = fact f l
            used (ThreadReturn _ l) f = fact f l
            used (CondBranch _ _ tl fl) f = fact f tl `S.union` fact f fl
            used Return{} f = fact_bot setLattice
            used Fail{} f = fact_bot setLattice

            fact :: FactBase (S.Set VarName) -> Label -> S.Set VarName
            fact f l = fromMaybe S.empty $ lookupFact l f 

getLiveVariables :: MidIRRepr -> FactBase Live
getLiveVariables midir = runGM $ evalStupidFuelMonad fb maxBound
    where
      fb :: (CheckpointMonad m, FuelMonad m) => m (FactBase Live)
      fb = do (_, factBase, _) <- analyzeAndRewriteBwd 
                                  getLiveVariablesPass
                                  (JustC mlabels)
                                  graph
                                  mapEmpty
              return factBase
      graph = midIRGraph midir 
      mlabels = (map methodEntry $ midIRMethods midir)
      
      getLiveVariablesPass :: (CheckpointMonad m, FuelMonad m) => BwdPass m MidIRInst Live
      getLiveVariablesPass = BwdPass
                             { bp_lattice = liveLattice
                             , bp_transfer = liveness
                             , bp_rewrite = noBwdRewrite }

getLitLabels :: MidIRRepr -> RM (FactBase (S.Set String))
getLitLabels midir 
    = do (_, factBase, _) <- analyzeAndRewriteBwd 
                             getLitLabelsPass
                             (JustC mlabels)
                             graph
                             mapEmpty
         return $ factBase
    where graph = midIRGraph midir 
          mlabels = (map methodEntry $ midIRMethods midir)


getLitLabelsPass :: (CheckpointMonad m, FuelMonad m)
                    => BwdPass m MidIRInst (S.Set String)
getLitLabelsPass = BwdPass
                   { bp_lattice = setLattice
                   , bp_transfer = getLabsTransfer
                   , bp_rewrite = noBwdRewrite }
    where
      getLabsTransfer :: BwdTransfer MidIRInst (S.Set String)
      getLabsTransfer = mkBTransfer used
          where
            used :: MidIRInst e x -> Fact x (S.Set String) -> S.Set String
            used Label{} f = f
            used PostEnter{} f = f
            used (Enter _ _ _) f = f
            used (Store _ _ expr) f = S.union (getLabs expr) f
            used (DivStore _ _ _ e1 e2) f = S.unions [getLabs e1, getLabs e2, f]
            used (IndStore _ e1 e2) f = S.unions [getLabs e1, getLabs e2, f]
            used (Call _ _ _ es) f = f `S.union` S.unions [getLabs e | e <- es]
            used (Callout _ _ _ es) f = f `S.union` S.unions [getLabs e | e <- es]
            used (Parallel _ l x _ ll) fs = fact fs l `S.union` fact fs ll
            used (Branch _ l) f = fact f l
            used (ThreadReturn _ l) f = fact f l
            used (CondBranch _ e tl fl) f = getLabs e `S.union` fact f tl `S.union` fact f fl
            used Return{} f = fact_bot setLattice
            used Fail{} f = fact_bot setLattice

            fact :: FactBase (S.Set String) -> Label -> S.Set String
            fact f l = fromMaybe S.empty $ lookupFact l f 
            
            getLabs :: MidIRExpr -> S.Set String
            getLabs = fold_EE f S.empty
                where f a (LitLabel _ s) = S.insert s a
                      f a _ = a

removeUnusedStrings :: MidIRRepr -> RM MidIRRepr
removeUnusedStrings midir@(MidIRRepr fields strs meths graph)
    = do labelBase <- getLitLabels midir
         let mlabels = map methodEntry meths
             labels = S.unions $ map (\l -> fromMaybe (error "blargh") $ lookupFact l labelBase) mlabels
             strs' = filter (\(s, _, _) -> s `S.member` labels) strs
         return $ midir { midIRStrings = strs' }

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
