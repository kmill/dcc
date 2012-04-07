{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Safe #-}
#endif

module Compiler.Hoopl.Label
  ( Label
  , freshLabel
  , LabelSet, LabelMap
  , FactBase, noFacts, lookupFact

  , uniqueToLbl -- MkGraph and GHC use only
  , lblToUnique -- GHC use only
  )

where

import Compiler.Hoopl.Collections
import Compiler.Hoopl.Unique

-----------------------------------------------------------------------------
--		Label
-----------------------------------------------------------------------------

newtype Label = Label { lblToUnique :: Unique }
  deriving (Eq, Ord)

uniqueToLbl :: Unique -> Label
uniqueToLbl = Label

instance Show Label where
  show (Label n) = "L" ++ show n

freshLabel :: UniqueMonad m => m Label
freshLabel = freshUnique >>= return . uniqueToLbl

-----------------------------------------------------------------------------
-- LabelSet

newtype LabelSet = LS UniqueSet deriving (Eq, Ord, Show)

instance IsSet LabelSet where
  type ElemOf LabelSet = Label

  setNull (LS s) = setNull s
  setSize (LS s) = setSize s
  setMember (Label k) (LS s) = setMember k s

  setEmpty = LS setEmpty
  setSingleton (Label k) = LS (setSingleton k)
  setInsert (Label k) (LS s) = LS (setInsert k s)
  setDelete (Label k) (LS s) = LS (setDelete k s)

  setUnion (LS x) (LS y) = LS (setUnion x y)
  setDifference (LS x) (LS y) = LS (setDifference x y)
  setIntersection (LS x) (LS y) = LS (setIntersection x y)
  setIsSubsetOf (LS x) (LS y) = setIsSubsetOf x y

  setFold k z (LS s) = setFold (k . uniqueToLbl) z s

  setElems (LS s) = map uniqueToLbl (setElems s)
  setFromList ks = LS (setFromList (map lblToUnique ks))

-----------------------------------------------------------------------------
-- LabelMap

newtype LabelMap v = LM (UniqueMap v) deriving (Eq, Ord, Show)

instance IsMap LabelMap where
  type KeyOf LabelMap = Label

  mapNull (LM m) = mapNull m
  mapSize (LM m) = mapSize m
  mapMember (Label k) (LM m) = mapMember k m
  mapLookup (Label k) (LM m) = mapLookup k m
  mapFindWithDefault def (Label k) (LM m) = mapFindWithDefault def k m

  mapEmpty = LM mapEmpty
  mapSingleton (Label k) v = LM (mapSingleton k v)
  mapInsert (Label k) v (LM m) = LM (mapInsert k v m)
  mapDelete (Label k) (LM m) = LM (mapDelete k m)

  mapUnion (LM x) (LM y) = LM (mapUnion x y)
  mapUnionWithKey f (LM x) (LM y) = LM (mapUnionWithKey (f . uniqueToLbl) x y)
  mapDifference (LM x) (LM y) = LM (mapDifference x y)
  mapIntersection (LM x) (LM y) = LM (mapIntersection x y)
  mapIsSubmapOf (LM x) (LM y) = mapIsSubmapOf x y

  mapMap f (LM m) = LM (mapMap f m)
  mapMapWithKey f (LM m) = LM (mapMapWithKey (f . uniqueToLbl) m)
  mapFold k z (LM m) = mapFold k z m
  mapFoldWithKey k z (LM m) = mapFoldWithKey (k . uniqueToLbl) z m

  mapElems (LM m) = mapElems m
  mapKeys (LM m) = map uniqueToLbl (mapKeys m)
  mapToList (LM m) = [(uniqueToLbl k, v) | (k, v) <- mapToList m]
  mapFromList assocs = LM (mapFromList [(lblToUnique k, v) | (k, v) <- assocs])

-----------------------------------------------------------------------------
-- FactBase

type FactBase f = LabelMap f

noFacts :: FactBase f
noFacts = mapEmpty

lookupFact :: Label -> FactBase f -> Maybe f
lookupFact = mapLookup
