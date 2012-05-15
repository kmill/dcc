{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

-- | These are an attempt at making general webs for arbitrary
-- liveness things.
module Dataflow.GenWebs where

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
import Debug.Trace


data DU a = DU { duVar :: a
               , duDef :: NodePtr
               , duUse :: NodePtr }
          | DUv { duVar :: a
                , duDef :: NodePtr } -- ^ Represents a definition which
                                     -- isn't used.
          deriving (Show, Eq, Ord)

data Web a = Web { webVar :: a
                 , webDUs :: S.Set (DU a)
                 , webDefs :: S.Set NodePtr
                 , webUses :: S.Set NodePtr }
             deriving (Show, Eq, Ord)

duToWeb :: DU a -> Web a
duToWeb du@(DU var def use)
    = Web var (S.singleton du) (S.singleton def) (S.singleton use)
duToWeb du@(DUv var def)
    = Web var (S.singleton du) (S.singleton def) S.empty

-- | Combines two webs
wUnion :: Ord a => Web a -> Web a -> Web a
wUnion (Web v1 dus1 defs1 uses1) (Web v2 dus2 defs2 uses2)
    = Web
      { webVar = v1
      , webDUs = dus1 `S.union` dus2
      , webDefs = defs1 `S.union` defs2
      , webUses = uses1 `S.union` uses2 }

-- | Checks whether a web is in a list of blocks
webInBlocks :: Web a -> S.Set Label -> Bool
webInBlocks web labels = all (\n -> S.member (nodeLabel n) labels) $
                         S.toList (webDefs web `S.union` webUses web)

websIntersectingBlocks :: Ord a => Webs a -> S.Set Label -> S.Set (WebID)
websIntersectingBlocks webs labels = S.fromList [k | (k, x) <- M.toList webs, webIntersectingBlocks x labels]

-- | Checks whether a web intersets a list of blocks (as in whether there are any defs or uses of the web in the blocks)
webIntersectingBlocks :: Ord a => Web a -> S.Set Label -> Bool
webIntersectingBlocks web labels = not $ S.null $ S.intersection labels defUseLabels 
    where defUseLabels = S.union (S.map nodeLabel $ webDefs web) (S.map nodeLabel $ webDefs web)


---
--- Interference graphs
---

type WebID = Int

data InterfGraph a = InterfGraph
    { igIDToWeb :: M.Map WebID (Web a)
    , igAdjLists :: M.Map WebID (S.Set WebID)
    , igWebTable :: WebTables a
    }

-- | Gets a web by id
igGetWeb :: WebID -> InterfGraph a -> Web a
igGetWeb i g = igIDToWeb g M.! i

-- | Gets the adjacency list of a web by id
igGetAdj :: WebID -> InterfGraph a -> S.Set WebID
igGetAdj i g = M.findWithDefault S.empty i $ igAdjLists g

-- | Gets all the web ids
igGetWebIDs :: InterfGraph a -> [WebID]
igGetWebIDs g = M.keys $ igIDToWeb g

-- | Checks whether two webs interfere
igInterferes :: WebID -> WebID -> InterfGraph a -> Bool
igInterferes i j g = j `S.member` (igGetAdj i g)

-- | Merges the second web into the first.
igMergeWebs :: WebID -> WebID -> InterfGraph a -> InterfGraph a
igMergeWebs i j g = g { igAdjLists = M.insertWith S.union i (igGetAdj j g) (igAdjLists g) }

instance Show a => Show (InterfGraph a) where
    show g = unlines $ map showAdj (igGetWebIDs g)
        where dispWeb i = show i ++ "." ++ show (webVar web)
                          ++ "\n    d:" ++ show (S.toList $ webDefs web) ++ "\n    u:" ++ show (S.toList $ webUses web)
                  where web = igGetWeb i g
              showAdj i = dispWeb i ++ arrayLike (map dispWebName $ S.toList $ igGetAdj i g) ++ "\n"
              arrayLike [] = ""
              arrayLike lst = if length lst < 6
                              then "\n   " ++ intercalate " " lst
                              else "\n   " ++ intercalate " " (take 6 lst) ++ arrayLike (drop 6 lst)
              dispWebName i = show i ++ ".<" ++ show (webVar web) ++ ">"
                  where web = igGetWeb i g

---
--- Building webs
---

type AliveDeadFun n a = forall e x. n e x -> Maybe ([a], [a])

-- | (dus, undefineds)
type DUBuildFact a = (S.Set (DU a), S.Set (a, NodePtr))

duLattice :: forall a. Ord a => DataflowLattice (DUBuildFact a)
duLattice = DataflowLattice
            { fact_name = "du lattice"
            , fact_bot = (S.empty, S.empty)
            , fact_join = joinProd joinSets joinSets }

duTransfer :: forall n a. (NonLocal n, Ord a) =>
              AliveDeadFun n a -> BwdTransfer (PNode n) (DUBuildFact a)
duTransfer aliveDeadFn = mkBTransfer3 fe fm fx
    where fe :: (PNode n) C O -> DUBuildFact a -> DUBuildFact a
          fe (PNode l n) f
              = handle l (aliveDeadFn n) f
                
          fm :: (PNode n) O O -> DUBuildFact a -> DUBuildFact a
          fm (PNode l n) f
              = handle l (aliveDeadFn n) f
                
          fx :: (PNode n) O C -> FactBase (DUBuildFact a) -> DUBuildFact a
          fx (PNode l n) fb
              = handle l (aliveDeadFn n) (joinOutFacts duLattice n fb)
          
          handle :: NodePtr
                 -> Maybe ([a], [a]) -- ^ the alive/dead (i.e., uses/defs) for the node
                 -> DUBuildFact a
                 -> DUBuildFact a
          handle l (Just (uses, defs)) (dus, tomatch)
              = let withdef d = S.map makeDU rps
                        where rps = S.filter (\(var, ptr) -> var == d) tomatch
                              makeDU (var, ptr) = DU var l ptr
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
                in ( S.unions [dus, ddu, ddvirtused]
                   , S.unions [tomatch', dtomatch] )
          handle l Nothing (dus, tomatch)
              = (S.empty, S.empty)

duPass :: (Show a, Ord a, NonLocal n, Monad m) => AliveDeadFun n a -> BwdPass m (PNode n) (DUBuildFact a)
duPass aliveDeadFn = BwdPass
                     { bp_lattice = duLattice
                     , bp_transfer = duTransfer aliveDeadFn
                     , bp_rewrite = noBwdRewrite }

collectDU :: forall a n. (Show a, Ord a, NonLocal n) =>
             AliveDeadFun n a -> [Label] -> Graph (PNode n) C C -> M.Map Label (S.Set (DU a))
collectDU aliveDeadFn mlabels graph
    = M.fromList $ map (\l -> (l, getDUs $ fromMaybe (error "GenWebs 1") $ lookupFact l f)) mlabels
      where f :: FactBase (DUBuildFact a)
            f = runGM $ evalStupidFuelMonad getf maxBound
            getf :: RM (FactBase (DUBuildFact a))
            getf = do (_, f, _) <- analyzeAndRewriteBwd
                                   (duPass aliveDeadFn)
                                   (JustC mlabels)
                                   graph
                                   mapEmpty
                      return f
            getDUs (a, b) = a

collectWebs :: forall a. Ord a => S.Set (DU a) -> [Web a]
collectWebs dus = iteration (M.keys webmap) webmap M.empty M.empty M.empty
    where webs = map duToWeb (S.toList dus)
          webmap = M.fromList $ zip [0..] webs
                    
          getAlias :: WebID -> M.Map WebID WebID -> WebID
          getAlias i aliases = case M.lookup i aliases of
                                 Nothing -> i
                                 Just j -> getAlias j aliases
          insertAlias :: WebID -> WebID -> M.Map WebID WebID -> M.Map WebID WebID
          insertAlias i j aliases | i == j = aliases
                                  | otherwise = M.insert i j aliases
          
          iteration :: [WebID] -- ^ webs to check
                       -> M.Map WebID (Web a) -- ^ all webs
                       -> M.Map (a, NodePtr) WebID -- ^ definitions
                       -> M.Map (a, NodePtr) WebID -- ^ uses
                       -> M.Map WebID WebID -- ^ aliases
                       -> [Web a]
          iteration tocheck webs defs uses aliases
              = case tocheck of
                  [] -> coalesceAliases M.empty (M.keys webs)
                      where coalesceAliases :: M.Map WebID (Web a) -> [WebID] -> [Web a]
                            coalesceAliases currmap []
                                = M.elems currmap
                            coalesceAliases currmap (w:ws)
                                = let w' = getAlias w aliases
                                      currmap' = M.insertWith wUnion w' (webs M.! w) currmap
                                  in coalesceAliases currmap' ws
                  w:ws -> let (w', defs', aliases') = handle (S.toList $ webDefs web) w defs aliases
                              (w'', uses', aliases'') = handle (S.toList $ webUses web) w' uses aliases'
                                   
                              web = webs M.! w
                              
                              handle :: [NodePtr] -> WebID -> M.Map (a, NodePtr) WebID -> M.Map WebID WebID
                                     -> (WebID, M.Map (a, NodePtr) WebID, M.Map WebID WebID)
                              handle [] w checkmap aliasmap = (w, checkmap, aliasmap)
                              handle (n:ns) w checkmap aliasmap
                                  = case M.lookup (webVar web, n) checkmap of
                                      Just w' -> let w'' = getAlias w' aliasmap
                                                 in handle ns w'' checkmap (insertAlias w w'' aliasmap)
                                      Nothing -> handle ns w (M.insert (webVar web, n) w checkmap) aliasmap
                                      
                          in iteration ws webs defs' uses' aliases''

type Webs a = M.Map WebID (Web a)

getWeb :: WebID -> Webs a -> Web a
getWeb i webs = webs M.! i

-- | Gets the webs in the graph
getWebs :: (Show a, NonLocal n, Ord a) => AliveDeadFun n a -> [Label] -> Graph (PNode n) C C -> Webs a
getWebs aliveDeadFn mlabels graph 
    = let dus = collectDU aliveDeadFn mlabels graph
          webs l = collectWebs (dus M.! l)
          allWebs = concatMap webs mlabels
      in M.fromList $ zip [0..] allWebs


-- First one is a map from defs to webs. Second one is a map from uses to webs
type WebTables a = (M.Map (a, NodePtr) WebID, M.Map (a, NodePtr) WebID)

makeTables :: Ord a => Webs a -> WebTables a
makeTables webs = (defs, uses) 
    where defs = M.fromList $ do (k, v) <- M.toList webs
                                 d <- S.toList $ webDefs v
                                 return ( (webVar v, d), k)
          uses = M.fromList $ do (k, v) <- M.toList webs 
                                 u <- S.toList $ webUses v 
                                 return ( (webVar v, u), k)

lookupVarUse :: Ord a => a -> NodePtr -> WebTables a -> WebID 
lookupVarUse v n (_, table) = table M.! (v, n)

lookupVarDef :: Ord a => a -> NodePtr -> WebTables a -> WebID 
lookupVarDef v n (table, _) = table M.! (v, n) 

-- | Builds the interference graph
makeInterfGraph :: (Ord a, NonLocal n) =>
                   [Label] -> Graph (PNode n) C C
                   -> Webs a -> M.Map NodePtr (S.Set WebID, S.Set WebID)
                   -> InterfGraph a
makeInterfGraph mlabels graph idToWebMap moves = InterfGraph idToWebMap adjs (makeTables idToWebMap)
    where idToWeb = M.toList idToWebMap
          
          combineUsedef (a1, b1) (a2, b2) = (a1 `S.union` a2, b1 `S.union` b2)
          
          addUse w u usedef = M.insertWith combineUsedef u (S.singleton w, S.empty) usedef
          addDef w d usedef = M.insertWith combineUsedef d (S.empty, S.singleton w) usedef
          
          -- | A map from nodes to (alive, dead) sets of WebIDs
          usedef = foldl (flip id) M.empty ([addDef w d | (w, web) <- idToWeb, d <- S.toList $ webDefs web]
                                            ++ [addUse w u | (w, web) <- idToWeb, u <- S.toList $ webUses web])
          
          -- | The adjacency lists!
          adjs = let adjm = buildAdjLists mlabels graph usedef moves
                 in M.unions [adjm M.! l | l <- mlabels]

type AdjListFact = (S.Set WebID, M.Map WebID (S.Set WebID))

buildAdjLists :: forall n. NonLocal n =>
                 [Label] -> Graph (PNode n) C C -> M.Map NodePtr (S.Set WebID, S.Set WebID)
              -> M.Map NodePtr (S.Set WebID, S.Set WebID) -- ^ move map
              -> M.Map Label (M.Map WebID (S.Set WebID))
buildAdjLists mlabels graph usedef moves
    = M.fromList $ map (\l -> (l, snd $ fromMaybe (error "GenWebs 2") $ lookupFact l facts)) mlabels
    where alLattice :: DataflowLattice AdjListFact
          alLattice = DataflowLattice
                      { fact_name = "alLattice"
                      , fact_bot = (S.empty, M.empty)
                      , fact_join = joinProd joinSets (joinMaps joinSets) }
          
          alTransfer :: BwdTransfer (PNode n) AdjListFact
          alTransfer = mkBTransfer3 fe fm fx
              where fe :: PNode n C O -> AdjListFact -> AdjListFact
                    fe (PNode l n) f = handle (M.findWithDefault (S.empty, S.empty) l usedef) f
                    fm :: PNode n O O -> AdjListFact -> AdjListFact
                    fm (PNode l n) f@(live, adj)
                        | l `M.member` moves
                            = let (alive, dead) = moves M.! l
                              in handle (alive, dead) (live S.\\ alive, adj)
                        | otherwise
                            = handle (M.findWithDefault (S.empty, S.empty) l usedef) f
                    fx :: PNode n O C -> FactBase AdjListFact -> AdjListFact
                    fx (PNode l n) fs = handle (M.findWithDefault (S.empty, S.empty) l usedef) 
                                        (joinOutFacts alLattice n fs)
                    
                    handle :: (S.Set WebID, S.Set WebID) -> AdjListFact -> AdjListFact
                    handle (alive, dead) (live, adj)
                        = let live' = live S.\\ dead
                              addEdge u v adjlist | u == v = adjlist
                                                  | otherwise = add u v $ add v u adjlist
                              add u v al = M.insertWith S.union u (S.singleton v) al
                              adj' = foldl (flip id) adj [addEdge d l
                                                         | d <- S.toList dead, l <- S.toList live]
                          in (alive `S.union` (live' S.\\ dead), adj')
          
          alPass :: Monad m => BwdPass m (PNode n) AdjListFact
          alPass = BwdPass
                   { bp_lattice = alLattice
                   , bp_transfer = alTransfer
                   , bp_rewrite = noBwdRewrite }
          doAL :: RM (FactBase AdjListFact)
          doAL = do (_, f, _) <- analyzeAndRewriteBwd
                                 alPass
                                 (JustC mlabels)
                                 graph
                                 mapEmpty
                    return f
          facts :: FactBase AdjListFact
          facts = runGM $ evalStupidFuelMonad doAL 2222222
