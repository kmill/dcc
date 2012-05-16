{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

module Dataflow.IRWebs where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.List
import Data.Maybe
import Data.Function
import Control.Monad
import DataflowTypes
import Dataflow.OptSupport
import AST(noPosition, SourcePos)
import IR
import Compiler.Hoopl
import Util.NodeLocate
import qualified Dataflow.GenWebs as G

type DU = G.DU VarName
type Web = G.Web VarName

webVar = G.webVar :: Web -> VarName
webDefs = G.webDefs :: Web -> S.Set NodePtr
webUses = G.webUses :: Web -> S.Set NodePtr

-- | Combines two webs
wUnion :: Web -> Web -> Web
wUnion = G.wUnion

-- | Checks whether a web is in a list of blocks
webInBlocks :: Web -> S.Set Label -> Bool
webInBlocks = G.webInBlocks

websIntersectingBlocks :: Webs -> S.Set Label -> S.Set WebID 
websIntersectingBlocks = G.websIntersectingBlocks

-- | Checks whether a web intersets a list of blocks (as in whether there are any defs or uses of the web in the blocks)
webIntersectingBlocks :: Web -> S.Set Label -> Bool  
webIntersectingBlocks = G.webIntersectingBlocks


type WebID = G.WebID

---
--- Building webs
---

type Webs = G.Webs VarName

getWeb :: WebID -> Webs -> Web
getWeb = G.getWeb

-- | Gets the webs in the graph
getWebs :: [Label] -> Graph (PNode MidIRInst) C C -> Webs
getWebs mlabels graph = G.getWebs getMidAliveDead mlabels graph


-- First one is a map from defs to webs. Second one is a map from uses to webs
type WebTables = G.WebTables VarName

makeTables :: Webs -> WebTables
makeTables = G.makeTables

lookupVarUse :: VarName -> NodePtr -> WebTables -> WebID 
lookupVarUse = G.lookupVarUse

lookupVarDef :: VarName -> NodePtr -> WebTables -> WebID 
lookupVarDef = G.lookupVarUse
