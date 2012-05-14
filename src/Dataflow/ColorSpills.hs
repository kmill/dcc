{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

module Dataflow.ColorSpills(performColorSpills) where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Int
import Data.Maybe
import Data.List
import Data.Either
import DataflowTypes
import Dataflow.OptSupport
import qualified IR as I
import Assembly
import Util.NodeLocate
import Compiler.Hoopl
import Dataflow.GenWebs
import AliveDead
import Debug.Trace

performColorSpills :: (CheckpointMonad m, FuelMonad m)
                        => LowIRRepr -> m LowIRRepr
performColorSpills asm
  = do let pg = toPGraph graph
           spillWebs = getWebs spillAliveDead mlabels pg
           spillTable = makeTables spillWebs
       (_, smvs, _) <- analyzeAndRewriteBwd
                       (collectSpillMovePass spillTable)
                       (JustC mlabels)
                       pg
                       mapEmpty
       let spillMoves = M.unions $ map (\l -> fst $ fromMaybe (error "ColorSpills") $ lookupFact l smvs) mlabels
           spillInterf = makeInterfGraph mlabels pg spillWebs spillMoves
           colors = combineSpills spillInterf spillMoves
           graph' = mapGraph (renameSpills colors spillInterf) pg
       return $ asm { lowIRGraph = graph' }
  where graph = lowIRGraph asm
        mlabels = (map I.methodEntry $ lowIRMethods asm)

renameSpills :: forall e x. M.Map WebID SpillLoc -> InterfGraph SpillLoc 
             -> PNode Asm e x -> Asm e x
renameSpills colors igraph (PNode l n)
    = case n of
        Spill pos r s -> Spill pos r (getColorDef s)
        Reload pos s r -> Reload pos (getColorUse s) r
        n' -> n'
      where getColorUse s = colors M.! lookupVarUse s l (igWebTable igraph)
            getColorDef s = colors M.! lookupVarDef s l (igWebTable igraph)

spillAliveDead :: forall e x. Asm e x -> ([SpillLoc], [SpillLoc])
spillAliveDead (Enter _ _ args _) = if args > 6
                                    then ([], lefts $ drop 6 (take args argLocation))
                                    else ([], [])
spillAliveDead (Spill _ _ s) = ([], [s])
spillAliveDead (Reload _ s _) = ([s], [])
spillAliveDead _ = ([], [])

-- This is of (moves, tomove)
type CollectSpillMoveFact = (M.Map NodePtr (S.Set WebID, S.Set WebID),
                             M.Map Reg (S.Set WebID))


-- | Collects a list of "spill moves"
collectSpillMovePass :: (CheckpointMonad m, FuelMonad m)
                        => WebTables SpillLoc
                        -> BwdPass m (PNode Asm) CollectSpillMoveFact
collectSpillMovePass spills
    = BwdPass
      { bp_lattice = getSpillMoveLattice
      , bp_transfer = getSpillMoveTransfer
      , bp_rewrite = noBwdRewrite }
    where
      getSpillMoveLattice :: DataflowLattice CollectSpillMoveFact
      getSpillMoveLattice = DataflowLattice
                            { fact_name = "Spill move lattice"
                            , fact_bot = (M.empty, M.empty)
                            , fact_join = joinProd (joinMaps (joinProd joinSets joinSets))
                                          (joinMaps joinSets) }
      getSpillMoveTransfer :: BwdTransfer (PNode Asm) CollectSpillMoveFact
      getSpillMoveTransfer = mkBTransfer3 usedCO usedOO usedOC
          where
            usedCO :: (PNode Asm) C O -> CollectSpillMoveFact -> CollectSpillMoveFact
            usedCO (PNode _ n) (moves, tomove) = (moves, remove dead tomove)
                where (_, dead) = getAliveDead n
            
            usedOO :: (PNode Asm) O O -> CollectSpillMoveFact -> CollectSpillMoveFact
            usedOO (PNode l (Reload _ s r)) (moves, tomove)
                = case M.lookup r tomove of
                    Just webs -> (moves', M.delete r tomove)
                        where spillID = lookupVarUse s l spills
                              moves' = M.insertWith update l
                                       (S.singleton spillID, webs)
                                       moves
                              update = S.union >< S.union
                    Nothing -> (moves, tomove)
            usedOO (PNode l (Spill _ r s)) (moves, tomove)
                = (moves, tomove')
                  where tomove' = M.insertWith S.union r (S.singleton spillID) tomove
                        spillID = lookupVarDef s l spills
            usedOO (PNode l n) (moves, tomove)
                = (moves, remove dead tomove)
                  where (_, dead) = getAliveDead n
            
            usedOC :: (PNode Asm) O C -> FactBase CollectSpillMoveFact -> CollectSpillMoveFact
            usedOC (PNode l n) fs = (moves, remove dead tomove)
                where (moves, tomove) = joinOutFacts getSpillMoveLattice n fs
                      (_, dead) = getAliveDead n
            
            remove :: Ord k => [k] -> M.Map k v -> M.Map k v
            remove items m = foldl (flip id) m (map M.delete items)


data SpillWorklists = SpillWorklists
    { swAliases :: M.Map WebID WebID
    , swMoves :: [(NodePtr, WebID, WebID)]
    , swWebs :: [WebID]
    , swColors :: M.Map WebID SpillLoc
    , swInterfGraph :: InterfGraph SpillLoc
    }
    deriving Show

swGetAlias :: WebID -> SpillWorklists -> WebID
swGetAlias i sw = case M.lookup i (swAliases sw) of
                    Just i' -> swGetAlias i' sw
                    Nothing -> i

-- | Main entry point for spill recoloring
combineSpills :: InterfGraph SpillLoc
              -> M.Map NodePtr (S.Set WebID, S.Set WebID)
              -> M.Map WebID SpillLoc
combineSpills graph moves
    = let sw = makeSpillWorklists graph moves
          sw' = mergeSpills sw
          sw'' = colorSpills sw'
      in swColors sw''
    where
      makeSpillWorklists :: InterfGraph SpillLoc
                         -> M.Map NodePtr (S.Set WebID, S.Set WebID)
                         -> SpillWorklists
      makeSpillWorklists graph moves
          = SpillWorklists
            { swAliases = M.empty
            , swMoves = do (l, (srcs, dests)) <- M.toList moves
                           s <- S.toList srcs
                           d <- S.toList dests
                           return (l, s, d)
            , swWebs = igGetWebIDs graph
            , swColors = M.empty
            , swInterfGraph = graph
            }

      addAlias :: WebID -> WebID -> SpillWorklists -> SpillWorklists
      addAlias u v sw
          = sw { swAliases = M.insert v u $ swAliases sw
               , swWebs = delete v $ swWebs sw
               , swInterfGraph = igMergeWebs u v $ swInterfGraph sw }

      mergeSpills :: SpillWorklists -> SpillWorklists
      mergeSpills sw
          = case swMoves sw of
              [] -> sw
              (l,s,d):mvs
                  | u == v -> mergeSpills sw'
                  | fixedWeb vweb || interferes -> mergeSpills sw'
                  | otherwise -> mergeSpills (addAlias u v sw')
                  where s' = swGetAlias s sw
                        d' = swGetAlias d sw
                        dweb = igGetWeb d' (swInterfGraph sw)
                        (u, v) = if fixedWeb dweb then (d', s') else (s', d')
                        vweb = igGetWeb v (swInterfGraph sw)
                        interferes = igInterferes u v (swInterfGraph sw)
                  
                        sw' = sw { swMoves = mvs }
                  
      fixedWeb web = fixedSpill (webVar web)

      colorSpills :: SpillWorklists -> SpillWorklists
      colorSpills sw
          = let sw' = emptyStack (swWebs sw) sw
                getAliasColor i = swColors sw' M.! swGetAlias i sw'
                webids = igGetWebIDs (swInterfGraph sw')
            in sw' { swColors = M.fromList $ map (\i -> (i, getAliasColor i)) $ webids }
          where emptyStack [] sw = sw
                emptyStack (i:is) sw
                    | fixedWeb web
                        = let sw' = sw { swColors = M.insert i (webVar web) $ swColors sw }
                          in emptyStack is sw'
                    | otherwise
                        = let adj = filter (`elem` swWebs sw) $
                                    S.toList $ igGetAdj i (swInterfGraph sw)
                              neighcolors = catMaybes $ map (`M.lookup` swColors sw') adj
                              okColors = freeSpillLocs \\ neighcolors
                              sw' = sw { swColors = M.insert i (head okColors) $ swColors sw }
                          in emptyStack is sw'
                    where web = igGetWeb i (swInterfGraph sw)
