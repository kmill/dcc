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


data DU = DU { duVar :: VarName
             , duDef :: NodePtr
             , duExtent :: S.Set NodePtr
             , duUse :: NodePtr }
        | DUv { duVar :: VarName
              , duDef :: NodePtr } -- ^ Represents a definition which
                                   -- isn't used.
          deriving (Show, Eq, Ord)

data Web = Web { webVar :: VarName
               , webDUs :: S.Set DU
               , webDefs :: S.Set NodePtr
               , webExtent :: S.Set NodePtr
               , webUses :: S.Set NodePtr }
           deriving (Show, Eq, Ord)

duToWeb du@(DU var def extent use)
    = Web var (S.singleton du) (S.singleton def) extent (S.singleton use)
duToWeb du@(DUv var def)
    = Web var (S.singleton du) (S.singleton def) S.empty S.empty

-- | Combines two webs
wUnion :: Web -> Web -> Web
wUnion (Web v1 dus1 defs1 ext1 uses1) (Web v2 dus2 defs2 ext2 uses2)
    = Web
      { webVar = v1
      , webDUs = dus1 `S.union` dus2
      , webDefs = defs1 `S.union` defs2
      , webExtent = ext1 `S.union` ext2
      , webUses = uses1 `S.union` uses2 }

-- | Checks whether two webs interfere
wInterf :: Web -> Web -> Bool
wInterf (Web v1 dus1 defs1 ext1 uses1) (Web v2 dus2 defs2 ext2 uses2)
    = (S.union defs1 ext1 `ints` S.union defs2 ext2)
      || (S.union ext1 uses1 `ints` S.union ext2 uses2)
    where ints s1 s2 = not $ S.null $ S.intersection s1 s2

-- | Checks whether a web is in a list of blocks
webInBlocks :: Web -> S.Set Label -> Bool
webInBlocks web labels = all (\n -> S.member (nodeLabel n) labels) $
                         S.toList (webDefs web `S.union` webUses web)

websIntersectingBlocks :: Webs -> S.Set Label -> S.Set WebID 
websIntersectingBlocks webs labels = S.fromList [k | (k, v) <- M.toList webs, webIntersectingBlocks v labels]

-- | Checks whether a web intersets a list of blocks (as in whether there are any defs or uses of the web in the blocks)
webIntersectingBlocks :: Web -> S.Set Label -> Bool  
webIntersectingBlocks web labels = not $ S.null $ S.intersection labels defUseLabels 
    where defUseLabels = S.union (S.map nodeLabel $ webDefs web) (S.map nodeLabel $ webDefs web)


type WebID = Int

data InterfGraph = InterfGraph
    { igIDToWeb :: M.Map WebID Web
    , igAdjLists :: M.Map WebID (S.Set WebID) }

-- | Gets a web by id
igGetWeb :: WebID -> InterfGraph -> Web
igGetWeb i g = igIDToWeb g M.! i

-- | Gets all the web ids
igGetWebIDs :: InterfGraph -> [WebID]
igGetWebIDs g = M.keys $ igIDToWeb g


---
--- Building webs
---

type DUBuildFact = (S.Set DU, S.Set (VarName, NodePtr), S.Set (VarName, NodePtr))

duLattice :: DataflowLattice DUBuildFact
duLattice = DataflowLattice
            { fact_name = "du lattice"
            , fact_bot = (S.empty, S.empty, S.empty)
            , fact_join = add }
    where add :: JoinFun DUBuildFact
          add _ (OldFact (oldDUs, oldUndefs, oldExtents)) (NewFact (newDUs, newUndefs, newExtents))
              = (ch, (dus', undefs', extents'))
              where dus' = S.union oldDUs newDUs
                    undefs' = S.union oldUndefs newUndefs
                    extents' = S.union oldExtents newExtents
                    bigger :: forall a. S.Set a -> S.Set a -> Bool
                    bigger = (>) `on` S.size
                    ch = changeIf (undefs' `bigger` oldUndefs
                                   || dus' `bigger` oldDUs
                                   || extents' `bigger` newExtents)

duTransfer :: BwdTransfer (PNode MidIRInst) DUBuildFact
duTransfer = mkBTransfer3 fe fm fx
    where fe :: (PNode MidIRInst) C O -> DUBuildFact -> DUBuildFact
          fe (PNode l n) f
              = handle l (getMidAliveDead n) f
                
          fm :: (PNode MidIRInst) O O -> DUBuildFact -> DUBuildFact
          fm (PNode l n) f
              = handle l (getMidAliveDead n) f
                
          fx :: (PNode MidIRInst) O C -> FactBase DUBuildFact -> DUBuildFact
          fx (PNode l n) fb
              = handle l (getMidAliveDead n) (joinOutFacts duLattice n fb)
          
          handle :: NodePtr
                 -> MidAliveDead -- ^ the alive/dead (i.e., uses/defs) for the node
                 -> DUBuildFact
                 -> DUBuildFact
          handle l (uses, defs) (dus, tomatch, extents)
              = let withdef d = S.map makeDU rps
                        where rps = S.filter (\(var, ptr) -> var == d) tomatch
                              makeDU (var, ptr) = DU var l (ptrs var) ptr
                    -- takes the NodePtrs from the current extents for a given variable
                    ptrs r = S.map snd $ S.filter (\(var, ptr) -> var == r) extents
                    -- we can remove things which have been defined
                    tomatch' = S.filter (\(var, ptr) -> var `notElem` defs) tomatch
                    -- we want to add the used things to the tomatch list
                    dtomatch = S.fromList $ map (\r -> (r, l)) uses
                    -- we add entries for things which are defined but
                    -- not used so caller-saved registers work
                    ddvirtused = S.fromList [DUv var l
                                            | var <- defs, var `S.notMember` matchvars]
                    matchvars = S.map (\(var, ptr) -> var) tomatch
                    -- these are the matched definitions to put in the
                    -- dus set
                    ddu = S.unions $ map withdef defs
                    -- we clear the extents list of things which have been defined
                    extents' = S.filter (\(var, ptr) -> var `notElem` defs) extents
                    -- and extend the list for those which are still there
                    dextents = S.map (\(var, ptr) -> (var, l)) tomatch'
                in ( S.unions [dus, ddu, ddvirtused]
                   , S.unions [tomatch', dtomatch]
                   , S.unions [extents', dextents] )

duPass :: Monad m => BwdPass m (PNode MidIRInst) DUBuildFact
duPass = BwdPass
         { bp_lattice = duLattice
         , bp_transfer = duTransfer
         , bp_rewrite = noBwdRewrite }

collectDU :: [Label] -> Graph (PNode MidIRInst) C C -> M.Map Label (S.Set DU)
collectDU mlabels graph
    = M.fromList $ map (\l -> (l, getDUs $ fromJust $ lookupFact l f)) mlabels
      where f :: FactBase DUBuildFact
            f = runGM $ evalStupidFuelMonad getf 2222222
            getf :: RM (FactBase DUBuildFact)
            getf = do (_, f, _) <- analyzeAndRewriteBwd
                                   duPass
                                   (JustC mlabels)
                                   graph
                                   mapEmpty
                      return f
            getDUs (a, b, c) = a

collectWebs :: S.Set DU -> [Web]
collectWebs dus = iteration (M.keys webmap) webmap M.empty M.empty M.empty
    where webs = map duToWeb (S.toList dus)
          webmap = M.fromList $ zip [0..] webs
          
          -- | Checks whether two webs should be coalesced because
          -- they have the same register and because they either share
          -- a definition or use.  If they are precolored webs, then
          -- they can be coalesced by the fact they have the same
          -- register.
          wToCoalesce :: Web -> Web -> Bool
          wToCoalesce (Web v1 dus1 ds1 ex1 us1)
                      (Web v2 dus2 ds2 ex2 us2)
              = v1 == v2 && (not (S.null $ ds1 `S.intersection` ds2)
                             || not (S.null $ us1 `S.intersection` us2))
          
          getAlias :: WebID -> M.Map WebID WebID -> WebID
          getAlias i aliases = case M.lookup i aliases of
                                 Nothing -> i
                                 Just j -> getAlias j aliases
          insertAlias :: WebID -> WebID -> M.Map WebID WebID -> M.Map WebID WebID
          insertAlias i j aliases | i == j = aliases
                                  | otherwise = M.insert i j aliases
          
          iteration :: [WebID] -- ^ webs to check
                       -> M.Map WebID Web -- ^ all webs
                       -> M.Map (VarName, NodePtr) WebID -- ^ definitions
                       -> M.Map (VarName, NodePtr) WebID -- ^ uses
                       -> M.Map WebID WebID -- ^ aliases
                       -> [Web]
          iteration tocheck webs defs uses aliases
              = case tocheck of
                  [] -> coalesceAliases M.empty (M.keys webs)
                      where coalesceAliases :: M.Map WebID Web -> [WebID] -> [Web]
                            coalesceAliases currmap []
                                = M.elems currmap
                            coalesceAliases currmap (w:ws)
                                = let w' = getAlias w aliases
                                      currmap' = M.insertWith wUnion w' (webs M.! w) currmap
                                  in coalesceAliases currmap' ws
                  w:ws -> let (w', defs', aliases') = handle (S.toList $ webDefs web) w defs aliases
                              (w'', uses', aliases'') = handle (S.toList $ webUses web) w' uses aliases'
                                   
                              web = webs M.! w
                              
                              handle :: [NodePtr] -> WebID -> M.Map (VarName, NodePtr) WebID -> M.Map WebID WebID
                                     -> (WebID, M.Map (VarName, NodePtr) WebID, M.Map WebID WebID)
                              handle [] w checkmap aliasmap = (w, checkmap, aliasmap)
                              handle (n:ns) w checkmap aliasmap
                                  = case M.lookup (webVar web, n) checkmap of
                                      Just w' -> let w'' = getAlias w' aliasmap
                                                 in handle ns w'' checkmap (insertAlias w w'' aliasmap)
                                      Nothing -> handle ns w (M.insert (webVar web, n) w checkmap) aliasmap
                                      
                          in iteration ws webs defs' uses' aliases''

type Webs = M.Map WebID Web

getWeb :: WebID -> Webs -> Web
getWeb i webs = webs M.! i

-- | Gets the webs in the graph
getWebs :: [Label] -> Graph (PNode MidIRInst) C C -> Webs
getWebs mlabels graph = let dus = collectDU mlabels graph
                            webs l = collectWebs (dus M.! l)
                            allWebs = concatMap webs mlabels
                        in M.fromList $ zip [0..] allWebs


-- First one is a map from defs to webs. Second one is a map from uses to webs
type WebTables = (M.Map (VarName, NodePtr) WebID, M.Map (VarName, NodePtr) WebID)

makeTables :: Webs -> WebTables
makeTables webs = (defs, uses) 
    where defs = M.fromList $ do (k, v) <- M.toList webs
                                 d <- S.toList $ webDefs v
                                 return ( (webVar v, d), k)
          uses = M.fromList $ do (k, v) <- M.toList webs 
                                 u <- S.toList $ webUses v 
                                 return ( (webVar v, u), k)

lookupVarUse :: VarName -> NodePtr -> WebTables -> WebID 
lookupVarUse v n (_, table) = table M.! (v, n)

lookupVarDef :: VarName -> NodePtr -> WebTables -> WebID 
lookupVarDef v n (table, _) = table M.! (v, n) 

-- -- | Builds the interference graph for all the webs by running wInterf
-- -- on all pairs of webs.
-- makeInterfGraph :: [Label] -> Graph (PNode MidIRInst) C C -> [Web] -> InterfGraph
-- makeInterfGraph mlabels graph webs = InterfGraph idToWebMap adjs
--     where idToWeb = zip [0..] webs
--           idToWebMap = M.fromList idToWeb
          
--           combineUsedef (a1, b1) (a2, b2) = (a1 `S.union` a2, b1 `S.union` b2)
          
--           addUse w u usedef = M.insertWith combineUsedef u (S.singleton w, S.empty) usedef
--           addDef w d usedef = M.insertWith combineUsedef d (S.empty, S.singleton w) usedef
          
--           -- | A map from nodes to (alive, dead) sets of WebIDs
--           usedef = foldl (flip id) M.empty ([addDef w d | (w, web) <- idToWeb, d <- S.toList $ webDefs web]
--                                             ++ [addUse w u | (w, web) <- idToWeb, u <- S.toList $ webUses web])
          
--           -- | The adjacency lists!
--           adjs = let adjm = buildAdjLists mlabels graph usedef
--                  in M.unions [adjm M.! l | l <- mlabels]