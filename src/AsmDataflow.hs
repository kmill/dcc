{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}

-- | Dataflow analyses on the lowir (Assembly.hs).
module AsmDataflow(performAsmDataflowAnalysis) where

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

import Dataflow.DeadCodeAsm
import Dataflow.ColorSpills
import Dataflow.BetterifyAsm
import Dataflow.BlockElimAsm

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
      , ADFA (hasOptFlag "betterifyasm") performBetterifyPass
      , ADFA (hasOptFlag "betterifyasm") performDeadAsmPass
      , ADFA (hasOptFlag "blockelimasm") performBlockElimAsm
      ]

performAsmDataflowAnalysis :: CompilerOpts -> LowIRRepr -> RM LowIRRepr
performAsmDataflowAnalysis copts lowir
    = foldl (>>=) (return lowir) (map (individualAnalysis opts) dataflows)
    where individualAnalysis :: OptFlags -> ADFA -> LowIRRepr -> RM LowIRRepr
          individualAnalysis opts (ADFA optCheck perform) lowir
              = if optCheck opts then perform lowir else return lowir
          opts = optMode copts