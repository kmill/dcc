{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}

module Dataflow.Flatten where

import Control.Monad
import qualified Data.Set as Set
import Compiler.Hoopl
import IR
import AST(SourcePos)
import Data.Maybe

nullLattice :: DataflowLattice ()
nullLattice = DataflowLattice
              { fact_name = "Null lattice (for flattener)"
              , fact_bot = ()
              , fact_join = (\ _ _ _ -> (NoChange, ())) }

nullTransfer :: FwdTransfer MidIRInst ()
nullTransfer = mkFTransfer ft
    where
      ft :: MidIRInst e x -> () -> Fact x ()
      ft (Branch _ l) f = mapSingleton l f
      ft (ThreadReturn _ l) f = mapSingleton l f
      ft (Parallel _ ll _ _ el) f = mkFactBase nullLattice
                                    [(el, ()), (ll, ())]
      ft (CondBranch _ _ tl fl) f = mkFactBase nullLattice
                                    [(tl, ()), (fl, ())]
      ft (Return _ _ _) f = mapEmpty
      ft (Fail _) f = mapEmpty
      ft Label{} f = f
      ft PostEnter{} f = f
      ft Enter{} f = f
      ft Store{} f = f
      ft DivStore{} f = f
      ft IndStore{} f = f
      ft Call{} f = f
      ft Callout{} f = f

nonTrivial :: Expr v -> Bool
nonTrivial (Load _ _) = True
nonTrivial (UnOp _ _ _) = True
nonTrivial (BinOp _ _ _ _) = True
nonTrivial _ = False

withTmp :: UniqueNameMonad m => SourcePos -> MidIRExpr -> (MidIRExpr -> MidIRInst O O)
        -> m (Maybe (Graph MidIRInst O O))
withTmp pos e f = do tmp <- genUniqueName "flatten"
                     return $ Just $ mkMiddles
                                [ Store pos (MV tmp) e
                                , f (Var pos (MV tmp)) ]

withTmpC :: UniqueNameMonad m => SourcePos -> MidIRExpr -> (MidIRExpr -> MidIRInst O C)
         -> m (Maybe (Graph MidIRInst O C))
withTmpC pos e f = do tmp <- genUniqueName "flatten"
                      return $ Just $ mkMiddle (Store pos (MV tmp) e)
                                 <*> mkLast (f (Var pos (MV tmp)))


flattenRewrite :: forall m. (FuelMonad m, UniqueNameMonad m)
                  => FwdRewrite m MidIRInst ()
flattenRewrite = deepFwdRw fl
    where
      fl :: MidIRInst e x -> () -> m (Maybe (Graph MidIRInst e x))
      fl (Label _ _) f = return Nothing
      fl (PostEnter _ _) f = return Nothing
      fl (Enter _ _ _) f = return Nothing
      fl (Store pos v e) f = flattenExpr e (\e' -> Store pos v e')
      fl (DivStore pos v op e1 e2) f
          | nonTrivial e1 = flattenExpr e1 (\e1' -> DivStore pos v op e1' e2)
          | nonTrivial e2 = flattenExpr e2 (\e2' -> DivStore pos v op e1 e2')
          | otherwise = return Nothing
      fl (IndStore pos dest src) f
          | nonTrivial dest = withTmp pos dest
                              (\dest' -> IndStore pos dest' src)
          | nonTrivial src = withTmp pos src
                             (\src' -> IndStore pos dest src')
          | otherwise = return Nothing
      fl (Call pos dest name args) f
          = doCall args []
            where doCall [] _ = return Nothing
                  doCall (a:as) fargs
                      | nonTrivial a = withTmp pos a
                                       (\dest' -> Call pos dest name
                                                  (reverse fargs ++ [dest'] ++ as))
                      | otherwise = doCall as (a:fargs)
      fl (Callout pos dest name args) f
          = doCall args []
            where doCall [] _ = return Nothing
                  doCall (a:as) fargs
                      | nonTrivial a = withTmp pos a
                                       (\dest' -> Callout pos dest name
                                                  (reverse fargs ++ [dest'] ++ as))
                      | otherwise = doCall as (a:fargs)
      fl (Branch _ _) f = return Nothing
      fl (ThreadReturn _ _) f = return Nothing
      fl (Parallel _ ll _ _ el) f = return Nothing
      fl (CondBranch pos e tl fl) f
          | nonTrivial e = withTmpC pos e
                           (\e' -> CondBranch pos e' tl fl)
          | otherwise = return Nothing
      fl (Return pos from (Just e)) f
          | nonTrivial e = withTmpC pos e
                           (\e' -> Return pos from (Just e'))
          | otherwise = return Nothing
      fl (Return _ from Nothing) f = return Nothing
      fl (Fail _) f = return Nothing


flattenExpr :: forall m. UniqueNameMonad m
               => MidIRExpr -> (MidIRExpr -> MidIRInst O O)
            -> m (Maybe (Graph MidIRInst O O))
flattenExpr (UnOp pos op e) f
    | nonTrivial e = withTmp pos e (\e' -> f $ UnOp pos op e')
    | otherwise = return Nothing
flattenExpr (BinOp pos op e1 e2) f
    | nonTrivial e1 = withTmp pos e1 (\e1' -> f $ BinOp pos op e1' e2)
    | nonTrivial e2 = withTmp pos e2 (\e2' -> f $ BinOp pos op e1 e2')
    | otherwise = return Nothing
flattenExpr (Load pos e) f
    | nonTrivial e = withTmp pos e (\e' -> f $ Load pos e')
    | otherwise = return Nothing
flattenExpr (Cond pos cexp texp fexp) f
    | nonTrivial cexp = withTmp pos fexp
                        (\fexp' -> f $ Cond pos cexp texp fexp')
    | nonTrivial texp = withTmp pos texp
                        (\texp' -> f $ Cond pos cexp texp' fexp)
    | nonTrivial cexp = withTmp pos cexp
                        (\cexp' -> f $ Cond pos cexp' texp fexp)
    | otherwise = return Nothing

flattenExpr _ _ = return Nothing
