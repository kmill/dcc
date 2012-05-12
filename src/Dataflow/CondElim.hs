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

data Assigned = InVar VarName
              | InRet

type AssignSet = CondSet (Assigned, Assignable)

condAssignLattice :: DataflowLattice AssignSet
condAssignLattice = DataflowLattice { fact_name = "Branch Assignments"
                                   , fact_bot = AssignSet (Just S.empty) (Just S.empty)
                                   , fact_join = add
                                   }
  where add _ (OldFact o@(AssignSet ol or)) (NewFact n@(AssignSet nl nr)) = (c, n')
          where c = n /= n'
                n'
                    | S.null or && S.null nr = CondSet ol nl
                    | otherwise = AssignSet Nothing Nothing
                          
condAssignness :: BwdTransfer MidIRInst AssignSet
condAssignness = mkBTransfer f
  where f :: MidIRInst e x -> Fact x AssignSet -> AssignSet
        f (Store v (Lit _ v')) k@(AssignSet (Just kr) kl) = CondSet (combineSets (singleton ((InVar v),(AssignCon v'))) kr)
        f (Store v (Var _ v')) k@(AssignSet (Just kr) kl) = CondSet (combineSets (singleton ((InVar v),(AssignVar v'))) kr)    
        f (Return _ (Just (Lit _ v')) k@(Assign (Just kr) kl) = CondSet (combineSets (singleton ((InRet, (AssignCon v')))) kr)
        f (Return _ (Just (Var _ v')) k@(Assign (Just kr) kl) = CondSet (combineSets (singleton ((InRet, (AssignVar v')))) kr)
        f _ k = AssignSet Nothing Nothing

combineSets :: 

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
