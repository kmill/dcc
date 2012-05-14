{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.CondElim where 

import qualified Data.Map as M

import Compiler.Hoopl
import IR
import Control.Monad
import Data.Maybe
import Debug.Trace
import Data.Int
import Text.ParserCombinators.Parsec (SourcePos)


data Assignable = AssignVar SourcePos VarName
                | AssignCon SourcePos Int64
                  deriving (Eq)
data Assigned = InVar VarName
              | InRet String
                deriving (Eq, Ord)

data AssignMap = AssignMap (Maybe (M.Map Assigned Assignable)) (Maybe (M.Map Assigned Assignable)) (Maybe Label)
               deriving (Eq)

condAssignLattice :: DataflowLattice AssignMap
condAssignLattice = DataflowLattice { fact_name = "Branch Assignments"
                                   , fact_bot = AssignMap (Just M.empty) (Just M.empty) Nothing
                                   , fact_join = add
                                   }
  where add _ (OldFact o@(AssignMap ol or fl)) (NewFact n@(AssignMap nl nr ll)) = (c, n')
          where c = changeIf (n' /= n)
                n'
                    | M.null (fromJust or) && M.null (fromJust nr) && fl == ll = AssignMap ol nl fl
                    | otherwise = AssignMap Nothing Nothing Nothing
                          
emptyCEFact :: AssignMap
emptyCEFact = fact_bot condAssignLattice

condAssignness :: BwdTransfer MidIRInst AssignMap
condAssignness = mkBTransfer f
  where f :: MidIRInst e x -> Fact x AssignMap -> AssignMap
        f (Store _ v (Lit p v')) k@(AssignMap (Just kr) kl lbl) = AssignMap (combineMaps (M.singleton (InVar v) (AssignCon p v')) kr) kl lbl
        f (Store _ v (Var p v')) k@(AssignMap (Just kr) kl lbl) = AssignMap (combineMaps (M.singleton (InVar v) (AssignVar p v')) kr) kl lbl
        f n'@(Return _ rx (Just (Lit p v'))) fb = AssignMap (combineMaps (M.singleton (InRet rx) (AssignCon p v')) kr) kl lbl
          where
            k@(AssignMap (Just kr) kl lbl) = joinOutFacts condAssignLattice n' fb        
        f n'@(Return _ rx (Just (Var p v'))) fb = AssignMap (combineMaps (M.singleton (InRet rx) (AssignVar p v')) kr) kl lbl
          where
            k@(AssignMap (Just kr) kl lbl) = joinOutFacts condAssignLattice n' fb        
        f (Branch _ lbl) kl = AssignMap (Just M.empty) (Just M.empty) (Just lbl)
        f _ k = AssignMap Nothing Nothing Nothing
        
combineMaps :: (M.Map Assigned Assignable) -> (M.Map Assigned Assignable) -> Maybe (M.Map Assigned Assignable)
combineMaps a b 
  | M.size (M.intersection a b) > 0 = Nothing
  | otherwise = Just (M.union a b)

condElim :: forall m . FuelMonad m => BwdRewrite m MidIRInst AssignMap
condElim = deepBwdRw ll
  where
    ll :: forall e x. MidIRInst e x -> Fact x AssignMap -> m (Maybe (Graph MidIRInst e x))
    ll n'@(CondBranch p ce tl fl) fb
        | M.size (M.intersection a b) == 1 && M.size a == 1 && M.size b == 1 = 
          case head (M.keys $ M.intersection a b) of 
            InRet r -> return $ Just $ mkLast $ Return p r (Just (Cond p ce (assignment (head $ M.elems a)) (assignment (head $ M.elems b))))
            InVar v -> case lbl' of
              Just lbl -> return $ Just $ (mkMiddle $ Store p v (Cond p ce (assignment (head $ M.elems a)) (assignment (head $ M.elems b)))) <*> (mkLast $ Branch p lbl)
              _ -> return Nothing
        | otherwise = return Nothing
            where
              f@(AssignMap (Just a) (Just b) lbl') = joinOutFacts condAssignLattice n' fb
    ll _ _ = return Nothing
    assignment :: Assignable -> Expr VarName
    assignment (AssignVar p x) = Var p x
    assignment (AssignCon p x) = Lit p x
