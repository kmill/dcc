{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}

module Dataflow.ConstProp where

import Dataflow.OptSupport
import Control.Monad
import qualified Data.Map as Map

import Compiler.Hoopl
import IR2
import AST(SourcePos, noPosition)
import Data.Int
import Data.Maybe 

type LitVal = (SourcePos, Int64)

type Node = MidIRInst 

-- Type and definition of the lattice
-- Need to figure out what "Var" Corresponds to 
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
varHasLit :: FwdTransfer Node ConstFact
varHasLit = mkFTransfer ft
    where
      ft :: MidIRInst e x -> ConstFact -> Fact x ConstFact
      ft (Label _ _) f = f
      ft (Enter _ _ args) f = Map.fromList (map (\a -> (a, Top)) args)
      ft (Store _ x (Lit pos k)) f = Map.insert x (PElem (pos, k)) f
      ft (Store _ x _) f = Map.insert x Top f
      ft (IndStore _ _ _) f = f
      ft (Call _ x _ _) f = Map.insert x Top f
      ft (Callout _ x _ _) f = Map.insert x Top f 
      ft (Branch _ l) f = mapSingleton l f
      ft (CondBranch _ (Var pos x) tl fl) f 
          = mkFactBase constLattice [ (tl, Map.insert x (PElem (pos, bTrue)) f)
                                    , (fl, Map.insert x (PElem (pos, bFalse)) f) ]
      ft (CondBranch _ _ tl fl) f 
          = mkFactBase constLattice [ (tl, f)
                                    , (fl, f) ]
      ft (Return _ _) f = mapEmpty
      ft (Fail _) f = mapEmpty


-- Rewrite function: replace constant variables
constProp :: forall m. FuelMonad m => FwdRewrite m Node ConstFact
constProp = mkFRewrite cp 
    where 
      cp :: Node e x -> ConstFact -> m (Maybe (Graph Node e x))
      cp node f 
             = return $ liftM insnToG $ mapVN (lookup f) node
      lookup :: ConstFact -> VarName -> Maybe MidIRExpr
      lookup f x = case Map.lookup x f of 
                     Just (PElem (pos, v)) -> Just $ Lit pos v
                     _ -> Nothing

simplify :: forall m f . FuelMonad m => FwdRewrite m Node f
simplify = deepFwdRw simp 
    where 
      simp :: forall e x. Node e x -> f -> m (Maybe (Graph Node e x))
      simp node _ = return $ liftM insnToG $ s_node node 
      s_node :: Node e x -> Maybe (Node e x)
      s_node (CondBranch pos (Lit _ x) tl fl) 
          = Just $ Branch pos (if intToBool x then tl else fl)
      s_node n = (mapEN . mapEE) s_exp n 
      s_exp (BinOp pos OpDiv expr (Lit _ 0)) 
          = Nothing
      s_exp (BinOp pos OpMod expr (Lit _ 0)) 
          = Nothing
      s_exp (BinOp pos op (Lit _ x1) (Lit _ x2)) 
          = Just $ Lit pos $ (binOp op) x1 x2
      s_exp (UnOp pos op (Lit _ x))
          = Just $ Lit pos $ (unOp op) x
      s_exp (Cond pos (Lit _ x) expt expf)
          = Just $ (if intToBool x then expt else expf)
      s_exp (Cond pos _ expt expf)
          | expt == expf  = Just expt
      s_exp _ = Nothing
      binOp OpAdd = (+)
      binOp OpSub = (-)
      binOp OpMul = (*)
      binOp OpDiv = div
      binOp OpMod = rem
      binOp CmpLT = \x y -> boolToInt $ x < y
      binOp CmpGT = \x y -> boolToInt $ x > y 
      binOp CmpLTE = \x y -> boolToInt $ x <= y 
      binOp CmpGTE = \x y -> boolToInt $ x >= y 
      binOp CmpEQ = \x y -> boolToInt $ x == y 
      binOp CmpNEQ = \x y -> boolToInt $ x /= y
      unOp OpNeg = negate 
      unOp OpNot = boolToInt . not . intToBool

