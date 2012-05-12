{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.CondElim where 

import qualified Data.Set as S

import Compiler.Hoopl
import IR
import Control.Monad
import Data.Maybe
import Debug.Trace


data CondSet a = CondSet (Maybe (S.Set a)) (Maybe (S.Set a))
data Assignable = AssignVar (Var SourcePos VarName)
                | AssignCon (Lit SourcePos Int64)

type AssignSet = CondSet (VarName, Assignable)

condAssignLattice :: DataflowLattice AssignSet
condAssignLattice = DataflowLattice { fact_name = "Branch Assignments"
                                   , fact_bot = CondSet (Just S.empty) (Just S.empty)
                                   , fact_join = add
                                   }
  where add _ (OldFact o) (NewFact n) = (c, n)
          where c = changeIf (o /= n)

lastLabelness :: BwdTransfer MidIRInst LastLabel
lastLabelness = mkBTransfer f
  where f :: MidIRInst e x -> Fact x LastLabel -> LastLabel
        f (Branch _ l) k = 
          case lookupFact l k of
            Just l' -> l' `mplus` Just l
            Nothing -> Just l
        f (Label _ l) (Just l')
            | l == l'  = Nothing
            | otherwise = Just l'
        f (PostEnter _ l) k = Nothing
        f (Label _ l) Nothing = Nothing
        f (Enter _ l _) k = Nothing
        
        f _ k = Nothing

--Special case of fromJust for Branch, since it could be removed in the previous transfer.
lastLabelElim :: forall m . FuelMonad m => BwdRewrite m MidIRInst LastLabel
lastLabelElim = deepBwdRw ll
  where
    ll :: MidIRInst e x -> Fact x LastLabel -> m (Maybe (Graph MidIRInst e x))
    ll (Branch p l) f = 
      return $ case lookupFact l f of
          Nothing -> Nothing
          Just mm -> mm >>= (Just . mkLast . (Branch p))
    ll (CondBranch p ce tl fl) f
        | tl == fl = return $ Just $ mkLast $ Branch p tl
        | otherwise =
            return $ do tl' <- fun tl
                        fl' <- fun fl
                        guard $ [tl', fl'] /= [tl, fl]
                        Just $ mkLast $ CondBranch p ce tl' fl'
        where
          fun :: Label -> Maybe Label
          --fun l = fromJust (lookupFact l f) `mplus` (Just l)
          fun l = fromMaybe (Just l) (lookupFact l f) `mplus` (Just l)
--    ll (Enter p l args) (Just l')
--        = return $ Just (mkFirst (Enter p l args)
--                         <*> mkLast (Branch p l'))
    ll _ f = return Nothing
