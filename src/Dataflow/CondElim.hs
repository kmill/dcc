{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.CondElim where 

import qualified Data.Map as M

import Compiler.Hoopl
import IR
import Control.Monad
import Data.Maybe
import Debug.Trace


data CondMap a b = CondSet (Maybe (M.Map a b)) (Maybe (M.Map a b))
data Assignable = AssignVar (Var SourcePos VarName)
                | AssignCon (Lit SourcePos Int64)
data Assigned = InVar VarName
              | InRet

type AssignMap = CondMap Assigned Assignable

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
                          
condAssignness :: BwdTransfer MidIRInst AssignMap
condAssignness = mkBTransfer f
  where f :: MidIRInst e x -> Fact x AssignMap -> AssignMap
        f (Store v (Lit _ v')) k@(AssignMap (Just kr) kl) = AssignMap (combineMaps (singleton ((InVar v),(AssignCon v'))) kr) kl
        f (Store v (Var _ v')) k@(AssignMap (Just kr) kl) = AssignMap (combineMaps (singleton ((InVar v),(AssignVar v'))) kr) kl 
        f (Return _ (Just (Lit _ v')) k@(AssignMap (Just kr) kl) = AssignMap (combineMaps (singleton ((InRet, (AssignCon v')))) kr) kl
        f (Return _ (Just (Var _ v')) k@(AssignMap (Just kr) kl) = AssignMap (combineMaps (singleton ((InRet, (AssignVar v')))) kr) kl
        f _ k = AssignMap Nothing Nothing

combineMaps :: (M.Map Assigned Assignable) -> (M.Map Assigned Assignable) -> Maybe (M.Map Assigned Assignable)
combineMaps a b 
  | M.size (M.intersection a b) > 0 = Nothing
  | otherwise = Just (M.union a b)

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
