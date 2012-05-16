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
                  deriving (Eq, Show)
data Assigned = InVar VarName
              | InRet String
                deriving (Eq, Ord, Show)

data AssignMap = AssignMap (Maybe (M.Map Assigned Assignable)) (Maybe (M.Map Assigned Assignable)) (Maybe Label)
               deriving (Eq, Show)

condAssignLattice :: DataflowLattice AssignMap
condAssignLattice = DataflowLattice { fact_name = "Branch Assignments"
                                   , fact_bot = AssignMap (Just M.empty) (Just M.empty) Nothing
                                   , fact_join = add
                                   }
  where add _ (OldFact o@(AssignMap (Just ol) (Just or) fl))
                (NewFact n@(AssignMap (Just nl) (Just nr) ll))
          = (c, n')
          where c = SomeChange
                n'
                  | M.null or && M.null nr = AssignMap (Just nl) (Just ol) lbl
                  | otherwise = AssignMap (Just M.empty) Nothing Nothing
                lbl = matchesMaybe fl ll
                matchesMaybe Nothing (Just x) = Just x
                matchesMaybe (Just x) Nothing = Just x
                matchesMaybe (Just x) (Just y)
                  | x == y = Just x
                  | otherwise = Nothing
                matchesMaybe _ _ = Nothing
        add _ _ _ = (c, n')
          where c = SomeChange
                n' = AssignMap Nothing Nothing Nothing
                
emptyCEFact :: AssignMap
emptyCEFact = fact_bot condAssignLattice

condAssignness :: BwdTransfer MidIRInst AssignMap
condAssignness = mkBTransfer f
  where f :: MidIRInst e x -> Fact x AssignMap -> AssignMap
        f n'@(Label p _) k = k
        f n'@(Store p v (Lit _ v')) k@(AssignMap (Just kr) kl lbl)
            = AssignMap (combineMaps (M.singleton (InVar v) (AssignCon p v'))
                         kr) kl lbl
        f n'@(Store p v (Var _ v')) fb = AssignMap (combineMaps (M.singleton (InVar v) (AssignVar p v')) kr) kl lbl
          where
            k@(AssignMap (Just kr) kl lbl) = fb        
        f n'@(Return _ rx (Just (Lit p v'))) fb = AssignMap (combineMaps (M.singleton (InRet rx) (AssignCon p v')) kr) kl lbl
          where
            k@(AssignMap (Just kr) kl lbl) = joinOutFacts condAssignLattice n' fb        
        f n'@(Return _ rx (Just (Var p v'))) fb = AssignMap (combineMaps (M.singleton (InRet rx) (AssignVar p v')) kr) kl lbl
          where
            k@(AssignMap (Just kr) kl lbl) = joinOutFacts condAssignLattice n' fb        
        f (Branch _ lbl) kl = AssignMap (Just M.empty) (Just M.empty) (Just lbl)
        f n@(CondBranch _ _ tl fl) k = (addFacts (fromMaybe (AssignMap Nothing Nothing Nothing) $ lookupFact tl k) (fromMaybe (AssignMap Nothing Nothing Nothing) $ lookupFact fl k))
          where addFacts o@(AssignMap (Just ol) (Just or) fl') n@(AssignMap (Just nl) (Just nr) ll') = n'
                  where n'
                          | M.null or && M.null nr = AssignMap (Just ol) (Just nl) lbl
                          | otherwise = AssignMap Nothing Nothing Nothing
                        lbl = matchesMaybe fl' ll'
                        matchesMaybe Nothing (Just x) = Just x
                        matchesMaybe (Just x) Nothing = Just x
                        matchesMaybe (Just x) (Just y)
                          | x == y = Just x
                          | otherwise = Nothing
                        matchesMaybe _ _ = Nothing
                addFacts _ _ = AssignMap Nothing Nothing Nothing
        f _ k = AssignMap (Just M.empty) (Just M.empty) Nothing
        
assignment :: Assignable -> Expr VarName
assignment (AssignVar p x) = Var p x
assignment (AssignCon p x) = Lit p x
