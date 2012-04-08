{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}

module Dataflow.CopyProp where

import Dataflow.OptSupport
import Control.Monad
import qualified Data.Set as S

import Compiler.Hoopl
import IR2
import AST(SourcePos, noPosition)
import Data.Int
import Data.Maybe 

type Node = MidIRInst 

type CopyFact = 
  
copyLattice :: DataflowLattice ConstFact
copyLattice = DataflowLattice { fact_name = "Copy Propagation Lattice"
                               , fact_bot = S.empty
                               , fact_join = S.union }
