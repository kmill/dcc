{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, FlexibleContexts #-}

-- | The 'Unify' module provides a somewhat general unification
-- algorithm for the 'Term' type inside instances of the
-- 'BindingMonad' class.  The algorithm only unifies tree-like
-- structures.  It could be extended to arbitrary pointed, ordered
-- structures, but such generality isn't useful for typechecking,
-- which was this module's intended purpose.
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

-- | Unification variable.
data UVar = UVar Int
            deriving (Eq, Ord)

instance Show UVar where
    show (UVar i) = "@" ++ show i

-- | Structures which can be unified by 'unify'.
data Term a = Var UVar
            | Term a [Term a]
              deriving (Eq, Show)

nullaryTerm :: a -> Term a
nullaryTerm x = Term x []

type UEnv a = Map.Map Int (Term a)

-- | This class does not need any implementation to define an
-- instance: the default definitions take advantage of each of the
-- typeclasses in the signature.  This typeclass defines functions
-- which make the 'unify' function work for its instances.
class ( Eq a
      , Monad m
      , Functor m
      , MonadState (UnifierData a) m)
    => BindingMonad a m | m -> a where
  
    -- | Generates a fresh unification variable that's guaranteed to
    -- be unique inside this 'BindingMonad'.
    genVar :: m UVar
    genVar = do us <- get
                put us { unifierVarCounter=unifierVarCounter us + 1 }
                return $ UVar (unifierVarCounter us)

    -- | Gets the binding associated with a particular unification
    -- variable.
    getBinding :: UVar -> m (Maybe (Term a))
    getBinding (UVar i) = do env <- unifierEnv <$> get
                             return $ Map.lookup i env

    -- | Binds a term to a unification variable.
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

-- | This function performs the "occurs check": whether a variable
-- occurs in a term to prevent cyclical bindings.
occursIn :: Eq a => UVar -> Term a -> Bool
occursIn v (Var v2) | v == v2 = True
                    | otherwise = False
occursIn v (Term _ xs) = any (occursIn v) xs

-- | The 'unify' function implements the unification algorithm.  It
-- follows the algorithm in "Correcting a Widespread Error in
-- Unification Algorithms" by Peter Norvig
-- (http://norvig.com/unify-bug.pdf).
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
