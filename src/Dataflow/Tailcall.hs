{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.Tailcall where

import Compiler.Hoopl
import IR
import AST(SourcePos)
import Control.Monad
import Data.Maybe
import Debug.Trace

tailcallPass :: (CheckpointMonad m, FuelMonad m, UniqueMonad m, UniqueNameMonad m) =>
                Label -> [VarName]
                -> BwdPass m MidIRInst LastReturn
tailcallPass postentry argvars
    = BwdPass
      { bp_lattice = lastReturnLattice
      , bp_transfer = lastReturnTransfer
      , bp_rewrite = tailcallElim postentry argvars }

data LastReturn = RUnknown
                | RJust String VarName
                | RAnything String
                | RMulti
                  deriving Eq
                  
combine RUnknown x = x
combine (RJust from v) RUnknown = RJust from v
combine (RJust from v) (RJust from' v') = if v == v' then RJust from v else RMulti
combine (RJust from v) (RAnything _) = RJust from v -- :-O basically should be an error
combine (RJust from v) RMulti = RMulti
combine (RAnything from) RUnknown = RAnything from
combine (RAnything _) (RJust from v) = RJust from v -- :-O basically should be an error
combine (RAnything _) RMulti = RMulti
combine _ _ = RMulti


lastReturnLattice :: DataflowLattice LastReturn
lastReturnLattice = DataflowLattice
                    { fact_name = "last returned variable"
                    , fact_bot = RUnknown
                    , fact_join = add
                    }
    where add _ (OldFact o) (NewFact n) = (c, f')
              where c = changeIf (o /= f')
                    f' = combine o n

lastReturnTransfer :: BwdTransfer MidIRInst LastReturn
lastReturnTransfer = mkBTransfer f
    where f :: MidIRInst e x -> Fact x LastReturn -> LastReturn
          f (Label _ l) k = k
          f (PostEnter _ l) k = k
          f (Enter _ _ _) k = k
          f (Store _ v _) k = case k of
                                RUnknown -> RUnknown
                                RJust from v' -> if v == v'
                                                 then RMulti
                                                 else RJust from v'
                                RAnything from -> RAnything from
                                RMulti -> RMulti
          f (DivStore _ v _ _ _) k = case k of
                                       RUnknown -> RUnknown
                                       RJust from v' -> if v == v'
                                                        then RMulti
                                                        else RJust from v'
                                       RAnything from -> RAnything from
                                       RMulti -> RMulti
          f IndStore{} k = RMulti
          f Call{} k = RMulti
          f Callout{} k = RMulti
          f (Branch _ l) k = fromMaybe RUnknown $ lookupFact l k
          f (CondBranch _ _ tl fl) k = combine tlf flf
            where tlf = fromMaybe RUnknown $ lookupFact tl k
                  flf = fromMaybe RUnknown $ lookupFact fl k
          f (Return _ from (Just (Var pos v))) k = RJust from v
          f (Return _ from Nothing) k = RAnything from
          f (Return _ from _) k = RMulti
          f (Fail _) k = RMulti

tailcallElim :: forall m. (UniqueNameMonad m, UniqueMonad m, FuelMonad m) =>
                Label -> [VarName]
             -> BwdRewrite m MidIRInst LastReturn
tailcallElim postentry argvars = mkBRewrite tc
    where
      tc :: MidIRInst e x -> Fact x LastReturn -> m (Maybe (Graph MidIRInst e x))
      tc Branch{} _ = return Nothing
      tc CondBranch{} _ = return Nothing
      tc (Call pos v name args) f
          = case f of
	     RJust funcname _
                | name == funcname  -> makeTailCall pos args
                | otherwise -> return Nothing
	     RAnything funcname
                | name == funcname  -> makeTailCall pos args
                | otherwise -> return Nothing
             _ -> return Nothing
      tc _ _ = return Nothing
      makeTailCall :: SourcePos -> [MidIRExpr] -> m (Maybe (Graph MidIRInst O O))
      makeTailCall pos args
          = do dl <- freshLabel
               tvars' <- replicateM (length argvars) (genUniqueName "tc")
               let tvars = map MV tvars'
               let tvarse = map (Var pos) tvars
               return $ Just $ catGraphs (map (mkstore pos) (zip tvars args))
                          <*> catGraphs (map (mkstore pos) (zip argvars tvarse))
                          <*> mkLast (Branch pos postentry)
                 
                   |*><*| mkFirst (Label pos dl)
      mkstore :: SourcePos -> (VarName, MidIRExpr) -> Graph MidIRInst O O
      mkstore pos (dv, sv) = mkMiddle $ Store pos dv sv
