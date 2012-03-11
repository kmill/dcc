-- | This module provides support for remembering the provenence of
-- data, which we call its "pedigree" since it's shorter than
-- "provenance".  Pedigreed data is an instance of Applicative and
-- Monad.
module Pedigree(Pedigreed, pedigree, pedigreeValue, withPedigree) where

import Control.Applicative
import qualified Data.Set as Set

-- | Pedigreed data has a set of its roots along with the value
-- itself.
data Pedigreed a b = Pedigreed { pedigree :: Set.Set a 
                               , pedigreeValue :: b }
                     deriving Show

instance Functor (Pedigreed a) where
  fmap f (Pedigreed sa vb) = Pedigreed sa (f vb)

instance Ord a => Applicative (Pedigreed a) where
    pure x = Pedigreed Set.empty x
    (Pedigreed sf vf) <*> (Pedigreed sb vb)
        = Pedigreed (Set.union sf sb) (vf vb)

instance Ord a => Monad (Pedigreed a) where
    return = pure
    (Pedigreed sa va) >>= f
        = case f va of
            Pedigreed sb vb ->
                Pedigreed (Set.union sa sb) vb

-- | Make a value pedigreed along with its initial entry in the
-- pedigree set.
withPedigree :: a -> b -> Pedigreed a b
withPedigree reason x = Pedigreed (Set.singleton reason) x


test1 = do a <- withPedigree "a" 4
           b <- withPedigree "b" 2
           return $ a + b

pedigreeMul :: (Ord a, Num b) => Pedigreed a b -> Pedigreed a b -> Pedigreed a b
pedigreeMul x@(Pedigreed _ 0) y = x
pedigreeMul x y@(Pedigreed _ 0) = y
pedigreeMul x y = (*) <$> x <*> y

test2 = [(withPedigree "x" 0) `pedigreeMul` (withPedigree "y" 2)
        ,(withPedigree "x" 2) `pedigreeMul` (withPedigree "y" 2)
        ,(withPedigree "x" 22) `pedigreeMul` (withPedigree "y" 0)]