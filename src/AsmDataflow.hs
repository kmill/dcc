{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}

-- | Dataflow analyses on the lowir (Assembly.hs).
module AsmDataflow(performAsmDataflowAnalysis) where

import Dataflow.DeadCodeAsm
import Dataflow.ColorSpills

import Control.Monad
import Data.Int
import qualified Data.Set as S
import qualified Data.Map as Map
import Data.Maybe

import Assembly
import Compiler.Hoopl
import Compiler.Hoopl.Fuel
import CLI
import DataflowTypes
--import Dataflow.GenWebs

---
---
---

data ADFA = ADFA
    { dfaOptCheck :: OptFlags -> Bool
    , dfaPerform :: LowIRRepr -> RM LowIRRepr }
    
dataflows :: [ADFA]
dataflows
    = [ ADFA (hasOptFlag "deadcodeasm") performDeadAsmPass
      , ADFA (hasOptFlag "colorspills") performColorSpills
      ]

performAsmDataflowAnalysis :: OptFlags -> LowIRRepr -> RM LowIRRepr
performAsmDataflowAnalysis opts lowir
    = foldl (>>=) (return lowir) (map (individualAnalysis opts) dataflows)
    where individualAnalysis :: OptFlags -> ADFA -> LowIRRepr -> RM LowIRRepr
          individualAnalysis opts (ADFA optCheck perform) lowir
              = if optCheck opts then perform lowir else return lowir