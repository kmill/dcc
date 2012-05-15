{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}

module Dataflow.CopyProp where

import qualified Data.Map as Map

import Compiler.Hoopl
import IR
import AST(SourcePos)
import Dataflow.OptSupport
import Control.Monad

type Node = MidIRInst 

type VarInfo = (SourcePos, VarName)
type CopyFact = Map.Map VarName (WithTop VarInfo)
copyLattice :: DataflowLattice CopyFact
copyLattice = DataflowLattice { fact_name = "Copy Propagation Lattice"
                               , fact_bot = Map.empty
                               , fact_join = joinMaps (extendJoinDomain copyFactAdd) }
    where copyFactAdd _ (OldFact (pos1, old)) (NewFact (_, new))
              = if new == old then (NoChange, PElem (pos1, old))
                else (SomeChange, Top)

emptyCopyFact :: CopyFact 
emptyCopyFact = fact_bot copyLattice 

-- Analysis: Whether a variable is a copy of another at a given point 
varIsCopy :: FwdTransfer MidIRInst CopyFact 
varIsCopy = mkFTransfer ft 
    where 
      ft :: MidIRInst e x -> CopyFact -> Fact x CopyFact 
      ft (Label _ _) f = f 
      ft (PostEnter _ _) f = f 
      ft (Enter _ _ args) f = Map.fromList (map (\a -> (a, Top)) args)
      ft (Store _ x (Var pos v)) f
        | x == v    = f
        | otherwise = removeBindingsTo x $ Map.insert x (PElem (pos, v)) f 
      ft (Store _ x _) f = removeBindingsTo x $ Map.insert x Top f 
      ft (DivStore _ x _ _ _) f = removeBindingsTo x $ Map.insert x Top f
      ft (IndStore _ _ _) f = f 
      ft (Call _ x _ _) f = removeBindingsTo x $ Map.insert x Top f 
      ft (Callout _ x _ _ ) f = removeBindingsTo x $ Map.insert x Top f 
      ft (Parallel _ ll var _ el) f
          = mkFactBase copyLattice 
              [ (ll, removeBindingsTo var $ Map.insert var Top f)
              , (el, f) ]
      ft (Branch _ l) f = mapSingleton l f 
      ft (ThreadReturn _ l) f = mapSingleton l emptyCopyFact
      ft (CondBranch _ _ tl fl) f 
             = mkFactBase copyLattice [ (tl, f)
                                      , (fl, f) ]
      ft (Return _ _ _) f = mapEmpty 
      ft (Fail _) f = mapEmpty 
      removeBindingsTo :: VarName -> CopyFact -> CopyFact 
      removeBindingsTo x oldMap = newMap 
          where newMap = Map.mapMaybe f oldMap 
                f (PElem (pos, v)) = if v == x 
                                     then Nothing 
                                     else Just $ PElem (pos, v)
                f v = Just v

-- Rewrite function: Replace copied variables with the original version 
copyProp :: forall m. FuelMonad m => FwdRewrite m MidIRInst CopyFact 
copyProp = mkFRewrite cp 
    where 
      cp :: MidIRInst e x -> CopyFact -> m (Maybe (Graph Node e x ))
      cp node f 
             = return $ liftM insnToG $ mapVN (copyLookup f) node 
      copyLookup :: CopyFact -> VarName -> Maybe MidIRExpr 
      copyLookup f x = case Map.lookup x f of 
                         Just (PElem (pos, v)) -> Just $ Var pos v 
                         _ -> Nothing
