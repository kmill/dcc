{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}

-- | This module uses the lattice which checks if a variable is
-- negative, zero, or positive.

module Dataflow.NZP where

import Dataflow.OptSupport
import Control.Monad
import qualified Data.Map as Map

import Compiler.Hoopl
import IR
import AST(SourcePos, noPosition, showPos)
import Data.Int
import Data.Maybe 

--type LitVal = (SourcePos, Int64)

data NZP' = Neg | Zero | Pos deriving Eq
type NZP = WithTopAndBot NZP'

-- Type and definition of the lattice
type NZPFact = Map.Map VarName NZP

nzpLattice :: DataflowLattice NZPFact
nzpLattice = DataflowLattice { fact_name = "nzp lattice"
                             , fact_bot = Map.empty 
                             , fact_join = joinMaps add }
    where add :: Label -> OldFact NZP -> NewFact NZP -> (ChangeFlag, NZP)
          add _ (OldFact old) (NewFact new)
              = case old of
                  Top -> (NoChange, Top)
                  Bot -> case new of
                           Bot -> (NoChange, Bot)
                           x -> (SomeChange, x)
                  PElem x -> case new of
                               Bot -> (NoChange, PElem x)
                               Top -> (SomeChange, Top)
                               PElem y
                                   | x == y -> (NoChange, PElem x)
                                   | otherwise -> (SomeChange, Top)


--initFact :: [VarName] -> ConstFact 
--initFact vars = Map.fromList $ [(v, Top) | v <- vars]

emptyNZPFact :: NZPFact
emptyNZPFact = fact_bot nzpLattice

-- Analysis: variable equals a literal constant
varHasNZP :: FwdTransfer MidIRInst NZPFact
varHasNZP = mkFTransfer ft
    where
      ft :: MidIRInst e x -> NZPFact -> Fact x NZPFact
      ft (Label _ _) f = f
      ft (PostEnter _ _) f = f
      ft (Enter _ _ args) f = Map.fromList (map (\a -> (a, Top)) args)
      ft (Store _ x expr) f = Map.insert x (nzpEval expr f) f
      ft (DivStore _ x op num den) f
          = let nzp1 = nzpEval num f
                nzp2 = nzpEval den f
                ev = case op of
                       DivQuo -> case combineNZP nzp1 nzp2 of
                                   Just (Neg, Neg) -> PElem Pos
                                   Just (Pos, Pos) -> PElem Pos
                                   Just (Neg, Pos) -> PElem Neg
                                   Just (Pos, Neg) -> PElem Neg
                                   Just (_, Zero) -> Top
                                   Just (Zero, _) -> PElem Zero
                                   _ -> Top
                       DivRem -> case combineNZP nzp1 nzp2 of
                                   Just (Neg, Neg) -> PElem Neg
                                   Just (Pos, Pos) -> PElem Pos
                                   Just (Neg, Pos) -> PElem Neg
                                   Just (Pos, Neg) -> PElem Pos
                                   Just (_, Zero) -> Top
                                   Just (Zero, _) -> PElem Zero
                                   _ -> Top
            in Map.insert x ev f
      ft (IndStore _ _ _) f = f
      ft (Call _ x _ _) f = Map.insert x Top f
      ft (Callout _ x _ _) f = Map.insert x Top f 
      ft (Branch _ l) f = mapSingleton l f
      ft (CondBranch _ (Var pos x) tl fl) f 
          = mkFactBase nzpLattice [ (tl, Map.insert x (PElem Pos) f)
                                  , (fl, Map.insert x (PElem Zero) f) ]
      ft (CondBranch _ _ tl fl) f 
          = mkFactBase nzpLattice [ (tl, f)
                                  , (fl, f) ]
      ft (Return _ _ _) f = mapEmpty
      ft (Fail _) f = mapEmpty

nzpEval :: MidIRExpr -> NZPFact -> NZP
nzpEval (Lit _ i) f
    | i < 0  = PElem Neg
    | i == 0 = PElem Zero
    | otherwise  = PElem Pos
nzpEval (Var _ v) f
    = case Map.lookup v f of
        Nothing -> error "NZP: expects all variables are defined before use! :-("
        Just x -> x
nzpEval (LitLabel _ _) f = PElem Pos -- assumption: memory locations are always positive
nzpEval (Load _ _) f = Top
nzpEval (UnOp _ OpNeg exp) f
    = case nzpEval exp f of
        PElem Neg -> PElem Pos
        PElem Zero -> PElem Zero
        PElem Pos -> PElem Neg
        _ -> Top
nzpEval (UnOp _ OpNot exp) f
    = case nzpEval exp f of
        PElem Zero -> PElem Pos
        PElem Pos -> PElem Zero
        PElem Neg -> error "NZP: expects not to not have negative argument"
        _ -> Top
nzpEval (BinOp pos op exp1 exp2) f
    = let nzp1 = nzpEval exp1 f
          nzp2 = nzpEval exp2 f
      in case op of
           OpAdd -> case combineNZP nzp1 nzp2 of
                      Just (Neg, Neg) -> PElem Neg
                      Just (Pos, Pos) -> PElem Pos
                      Just (Zero, x) -> PElem x
                      Just (x, Zero) -> PElem x
                      _ -> Top
           OpSub -> case combineNZP nzp1 nzp2 of
                      Just (Neg, Pos) -> PElem Neg
                      Just (Pos, Neg) -> PElem Pos
                      Just (Zero, x) -> case x of
                                          Pos -> PElem Neg
                                          Zero -> PElem Zero
                                          Neg -> PElem Pos
                      Just (x, Zero) -> PElem x
                      _ -> Top
           OpMul -> case combineNZP nzp1 nzp2 of
                      Just (Neg, Neg) -> PElem Pos
                      Just (Pos, Pos) -> PElem Pos
                      Just (Neg, Pos) -> PElem Neg
                      Just (Pos, Neg) -> PElem Neg
                      Just (Zero, _) -> PElem Zero
                      Just (_, Zero) -> PElem Zero
                      _ -> Top
           CmpLT -> case combineNZP nzp1 nzp2 of
                      Just (Neg, Zero) -> PElem Pos
                      Just (Zero, Neg) -> PElem Zero
                      Just (Neg, Pos) -> PElem Pos
                      Just (Pos, Neg) -> PElem Zero
                      Just (Zero, Pos) -> PElem Pos
                      Just (Pos, Zero) -> PElem Zero
                      Just (Zero, Zero) -> PElem Zero
                      _ -> Top
           CmpGT -> case combineNZP nzp1 nzp2 of
                      Just (Neg, Zero) -> PElem Zero
                      Just (Zero, Neg) -> PElem Pos
                      Just (Neg, Pos) -> PElem Zero
                      Just (Pos, Neg) -> PElem Pos
                      Just (Zero, Pos) -> PElem Zero
                      Just (Pos, Zero) -> PElem Pos
                      Just (Zero, Zero) -> PElem Zero
                      _ -> Top
           CmpLTE -> case combineNZP nzp1 nzp2 of
                       Just (Neg, Zero) -> PElem Pos
                       Just (Zero, Neg) -> PElem Zero
                       Just (Neg, Pos) -> PElem Pos
                       Just (Pos, Neg) -> PElem Zero
                       Just (Zero, Pos) -> PElem Pos
                       Just (Pos, Zero) -> PElem Zero
                       Just (Zero, Zero) -> PElem Pos
                       _ -> Top
           CmpGTE -> case combineNZP nzp1 nzp2 of
                       Just (Neg, Zero) -> PElem Zero
                       Just (Zero, Neg) -> PElem Pos
                       Just (Neg, Pos) -> PElem Zero
                       Just (Pos, Neg) -> PElem Pos
                       Just (Zero, Pos) -> PElem Zero
                       Just (Pos, Zero) -> PElem Pos
                       Just (Zero, Zero) -> PElem Pos
                       _ -> Top
           CmpEQ -> case combineNZP nzp1 nzp2 of
                      Just (Zero, Zero) -> PElem Pos
                      Just (Zero, _) -> PElem Zero
                      Just (_, Zero) -> PElem Zero
                      Just (Neg, Pos) -> PElem Zero
                      Just (Pos, Neg) -> PElem Zero
                      _ -> Top
           CmpNEQ -> case combineNZP nzp1 nzp2 of
                       Just (Zero, Zero) -> PElem Zero
                       Just (Zero, _) -> PElem Pos
                       Just (_, Zero) -> PElem Pos
                       Just (Neg, Pos) -> PElem Pos
                       Just (Pos, Neg) -> PElem Pos
                       _ -> Top


combineNZP :: NZP -> NZP -> Maybe (NZP', NZP')
combineNZP Top _ = Nothing
combineNZP _ Top = Nothing
combineNZP Bot _ = Nothing
combineNZP _ Bot = Nothing
combineNZP (PElem a) (PElem b) = Just (a, b)


nzpSimplify :: forall m f . FuelMonad m => FwdRewrite m MidIRInst NZPFact
nzpSimplify = mkFRewrite simp 
    where 
      simp :: forall e x. MidIRInst e x -> NZPFact -> m (Maybe (Graph MidIRInst e x))
      simp Label{} _ = return Nothing
      simp Enter{} _ = return Nothing
      simp PostEnter{} _ = return Nothing
      simp Store{} _ = return Nothing
      simp DivStore{} _ = return Nothing
      simp IndStore{} _ = return Nothing
      simp Call{} _ = return Nothing
      simp Callout{} _ = return Nothing
      simp Branch{} f = return Nothing
      simp (CondBranch pos expr tl fl) f
          = case nzpEval expr f of
              PElem Pos -> return $ Just $ mkLast $ Branch pos tl
              PElem Zero -> return $ Just $ mkLast $ Branch pos fl
              PElem Neg -> error "NZP: cond branch shouldn't get negative"
              _ -> return Nothing
      simp Return{} _ = return Nothing
      simp Fail{} _ = return Nothing
