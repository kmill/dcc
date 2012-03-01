{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, FlexibleContexts #-}

module Unify( Term(..)
            , UnificationError(..)
            , UnifierData(..)
            , newUnifierData
            , BindingMonad(..)
            , nullaryTerm
            , unify 
            , expandTerm
            )
       where

import qualified Data.Map as Map

import Control.Applicative
import Control.Monad.State
import Control.Monad.Error

data UVar = UVar Int
            deriving (Eq, Ord)

instance Show UVar where
    show (UVar i) = "@" ++ show i

data Term a = Var UVar
            | Term a [Term a]
              deriving (Eq, Show)
                       
nullaryTerm :: a -> Term a
nullaryTerm x = Term x []

type UEnv a = Map.Map Int (Term a)

class ( Eq a
      , Monad m
      , Functor m
      , MonadState (UnifierData a) m)
    => BindingMonad a m | m -> a where
  
    genVar :: m UVar
    genVar = do us <- get
                put us { unifierVarCounter=unifierVarCounter us + 1 }
                return $ UVar (unifierVarCounter us)

    getBinding :: UVar -> m (Maybe (Term a))
    getBinding (UVar i) = do env <- unifierEnv <$> get
                             return $ Map.lookup i env

    addBinding :: UVar -> Term a -> m ()
    addBinding (UVar i) t
        = do d <- get
             put $ d { unifierEnv = Map.insert i t (unifierEnv d) }
             return ()


data UnifierData a = UnifierData
    { unifierEnv :: UEnv a
    , unifierVarCounter :: Int
    } deriving Show

newUnifierData :: UnifierData a
newUnifierData = UnifierData
                 { unifierEnv=Map.empty
                 , unifierVarCounter=0 }

data UnificationError a = UHeadError (Term a) (Term a)
                        | UMismatchedLengths (Term a) (Term a)
                        | UOccursError UVar (Term a)
                deriving Show

expandTerm :: Eq a => Term a -> UEnv a -> Term a
expandTerm (Var (UVar i)) env
    = case Map.lookup i env of
        Just b -> expandTerm b env
        Nothing -> (Var (UVar i))
expandTerm (Term x xs) env = Term x [expandTerm x' env | x' <- xs]


occursIn :: Eq a => UVar -> Term a -> Bool
occursIn v (Var v2) | v == v2 = True
                    | otherwise = False
occursIn v (Term _ xs) = any (occursIn v) xs

unify :: ( BindingMonad a m
         , Applicative m
         , MonadError (UnificationError a) m)
         => Term a -> Term a -> m (Term a)
unify (Term x xs) (Term y ys)
    | x == y && length xs == length ys
        = Term x <$> sequence [unify x' y' | (x',y') <- zip xs ys]
    | x == y    = throwError $ UMismatchedLengths (Term x xs) (Term y ys)
    | otherwise = throwError $ UHeadError (Term x xs) (Term y ys)
unify (Var v) y = unifyVar v y
unify x (Var v) = unifyVar v x

unifyVar :: ( BindingMonad a m
            , Applicative m
            , MonadError (UnificationError a) m)
            => UVar -> Term a -> m (Term a)
unifyVar v1 (Var v2)
    | v1 == v2  = return $ Var v1
    | otherwise = do mb1 <- getBinding v1
                     case mb1 of
                       Just b1 -> unify b1 (Var v2)
                       Nothing ->
                           do mb2 <- getBinding v2
                              case mb2 of
                                Just b2 -> unify (Var v1) b2
                                Nothing -> do addBinding v1 (Var v2)
                                              return $ Var v2
unifyVar v t = do mb <- getBinding v
                  case mb of
                    Just b -> unify b t
                    Nothing ->
                        if v `occursIn` t
                        then throwError $ UOccursError v t
                        else do addBinding v t
                                return t
