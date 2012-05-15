{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}

module Dataflow.ConstProp where

import Dataflow.OptSupport
import Control.Monad
import qualified Data.Map as Map

import Compiler.Hoopl
import IR
import AST(SourcePos, noPosition)
import Data.Int
import Data.Maybe 

import AlgSimplify

type LitVal = (SourcePos, Int64)

-- Type and definition of the lattice
type ConstFact = Map.Map VarName (WithTop LitVal)
constLattice :: DataflowLattice ConstFact
constLattice = DataflowLattice { fact_name = "Constant Propagation Lattice (Arhrhrhghg)"
                               , fact_bot = Map.empty 
                               , fact_join = joinMaps (extendJoinDomain constFactAdd) }
    where constFactAdd _ (OldFact old) (NewFact new) = if new == old then (NoChange, PElem new)
                                                       else (SomeChange, Top)

initFact :: [VarName] -> ConstFact 
initFact vars = Map.fromList $ [(v, Top) | v <- vars]

emptyFact :: ConstFact 
emptyFact = fact_bot constLattice

-- Analysis: variable equals a literal constant
varHasLit :: FwdTransfer MidIRInst ConstFact
varHasLit = mkFTransfer ft
    where
      ft :: MidIRInst e x -> ConstFact -> Fact x ConstFact
      ft (Label _ _) f = f
      ft (PostEnter _ _) f = f
      ft (Enter _ _ args) f = Map.fromList (map (\a -> (a, Top)) args)
      ft (Store _ x (Lit pos k)) f = Map.insert x (PElem (pos, k)) f
      ft (Store _ x _) f = Map.insert x Top f
      ft (DivStore _ x _ _ _) f = Map.insert x Top f
      ft (IndStore _ _ _) f = f
      ft (Call _ x _ _) f = Map.insert x Top f
      ft (Callout _ x _ _) f = Map.insert x Top f 
      ft (Parallel _ ll var _ el) f
          = mkFactBase constLattice [ (ll, Map.insert var Top f)
                                    , (el, f) ]
      ft (Branch _ l) f = mapSingleton l f
      ft (ThreadReturn _ l) f = mapSingleton l emptyFact
      ft (CondBranch _ (Var pos x) tl fl) f 
          = mkFactBase constLattice [ (tl, Map.insert x (PElem (pos, bTrue)) f)
                                    , (fl, Map.insert x (PElem (pos, bFalse)) f) ]
      ft (CondBranch _ _ tl fl) f 
          = mkFactBase constLattice [ (tl, f)
                                    , (fl, f) ]
      ft (Return _ _ _) f = mapEmpty
      ft (Fail _) f = mapEmpty


-- Rewrite function: replace constant variables
constProp :: forall m. FuelMonad m => FwdRewrite m MidIRInst ConstFact
constProp = mkFRewrite cp 
    where 
      cp :: MidIRInst e x -> ConstFact -> m (Maybe (Graph MidIRInst e x))
      cp node f 
             = return $ liftM insnToG $ mapVN (lookup f) node
      lookup :: ConstFact -> VarName -> Maybe MidIRExpr
      lookup f x = case Map.lookup x f of 
                     Just (PElem (pos, v)) -> Just $ Lit pos v
                     _ -> Nothing

simplify :: forall m f . FuelMonad m => FwdRewrite m MidIRInst f
simplify = deepFwdRw simp 
    where 
      simp :: forall e x. MidIRInst e x -> f -> m (Maybe (Graph MidIRInst e x))
      simp node _ = return $ liftM insnToG $ algSimplifyInst node
