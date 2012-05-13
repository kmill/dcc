{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.CondElim where 

import qualified Data.Map as M

import Compiler.Hoopl
import IR
import Control.Monad
import Data.Maybe
import Debug.Trace


data Assignable = AssignVar (Var SourcePos VarName)
                | AssignCon (Lit SourcePos Int64)
data Assigned = InVar VarName
              | InRet String

data AssignMap = AssignMap (Maybe (M.Map Assigned Assignable)) (Maybe (M.Map Assigned Assignable))

condAssignLattice :: DataflowLattice AssignMap
condAssignLattice = DataflowLattice { fact_name = "Branch Assignments"
                                   , fact_bot = AssignMap (Just M.empty) (Just M.empty)
                                   , fact_join = add
                                   }
  where add _ (OldFact o@(AssignMap ol or)) (NewFact n@(AssignMap nl nr)) = (c, n')
          where c = n /= n'
                n'
                    | M.null or && M.null nr = AssignMap ol nl
                    | otherwise = AssignMap Nothing Nothing
                          
emptyCEFact :: AssignMap
emptyCEFact = fact_bot condAssignLattice

condAssignness :: BwdTransfer MidIRInst AssignMap
condAssignness = mkBTransfer f
  where f :: MidIRInst e x -> Fact x AssignMap -> AssignMap
        f (Store v (Lit _ v')) k@(AssignMap (Just kr) kl) = AssignMap (combineMaps (M.singleton (InVar v) AssignCon v') kr) kl
        f (Store v (Var _ v')) k@(AssignMap (Just kr) kl) = AssignMap (combineMaps (M.singleton (InVar v) AssignVar v') kr) kl 
        f (Return _ rx (Just (Lit _ v'))) k@(AssignMap (Just kr) kl) = AssignMap (combineMaps (M.singleton (InRet rx) AssignCon v') kr) kl
        f (Return _ rx (Just (Var _ v'))) k@(AssignMap (Just kr) kl) = AssignMap (combineMaps (M.singleton (InRet rx) AssignVar v') kr) kl
        f (Branch _ lbl) kl = AssignMap (Just M.empty) (Just M.empty)
        f _ k = AssignMap Nothing Nothing

combineMaps :: (M.Map Assigned Assignable) -> (M.Map Assigned Assignable) -> Maybe (M.Map Assigned Assignable)
combineMaps a b 
  | M.size (M.intersection a b) > 0 = Nothing
  | otherwise = Just (M.union a b)

condElim :: forall m . FuelMonad m => BwdRewrite m MidIRInst AssignMap
condElim = deepBwdRw ll
  where
    ll :: MidIRInst e x -> Fact x AssignMap -> m (Maybe (Graph MidIRInst e x))
    ll (CondBranch p ce tl fl) f@(AssignMap a b)
        | M.size (M.intersection a b) == 1 && M.size a == 1 && M.size b == 1 = 
          case first (M.keys $ M.intersection a b) of 
            InRet r -> return $ mkLast $ Return p r (Just (Cond p ce (first $ M.elems a) (first $ M.elems b)))
            InVar v -> return $ mkLast $ Store p v (Cond p ce (first $ M.elems a) (first $ M.elems b))
        | otherwise = return Nothing
    ll _ f = return Nothing
