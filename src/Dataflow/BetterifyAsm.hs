{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

-- | This is essentially constant/copy propagation
module Dataflow.BetterifyAsm(performBetterifyPass) where

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
import RegAlloc.InterfGraph(getPinned)

performBetterifyPass :: (CheckpointMonad m, FuelMonad m)
                     => LowIRRepr -> m LowIRRepr
performBetterifyPass asm
    = do graph' <- performBetterifyPass' mlabels graph
         return $ asm { lowIRGraph = graph' }
    where graph = lowIRGraph asm
          mlabels = (map I.methodEntry $ lowIRMethods asm)

performBetterifyPass' :: (CheckpointMonad m, FuelMonad m)
                         => [Label] -> Graph Asm C C -> m (Graph Asm C C)
performBetterifyPass' mlabels graph
    = do (graph', _, _) <- analyzeAndRewriteFwd
                           betterifySpills
                           (JustC mlabels)
                           graph
                           (mapFromList (map (\l -> (l, fact_bot betterifyLattice)) mlabels))
         return graph'

data BetterifyLoc = BInt64 Int64
                  | BSpill SpillLoc
                  | BReg Reg
                    deriving (Eq, Ord, Show)
type BetterifyFact = ( M.Map SpillLoc (WithTop BetterifyLoc)
                     , M.Map Reg (WithTop BetterifyLoc))

betterifyLattice :: DataflowLattice BetterifyFact
betterifyLattice = DataflowLattice
                   { fact_name = "betterify lattice"
                   , fact_bot = (M.empty, M.empty)
                   , fact_join = joinProd
                                 (joinMaps (extendJoinDomain add))
                                 (joinMaps (extendJoinDomain add)) }
    where add _ (OldFact bl1) (NewFact bl2)
              = if bl1 == bl2
                then (NoChange, PElem bl1)
                else (SomeChange, Top)

betterifySpills :: forall m. (CheckpointMonad m, FuelMonad m) =>
                   FwdPass m Asm BetterifyFact
betterifySpills = FwdPass
                  { fp_lattice = betterifyLattice
                  , fp_transfer = mkFTransfer3 ftCO ftOO ftOC
                  , fp_rewrite = rewrite }
    where 
          ftCO :: Asm C O -> BetterifyFact -> BetterifyFact
          ftCO (Enter _ _ numargs _) (spills, regs)
              = (spills'', regs')
                where spills' = M.fromList $ map (\a -> (a, Top)) $ 
                                lefts $ drop 6 $ take numargs argLocation
                      spills'' = if numargs > 6 then spills' else M.empty
                      regs' = M.fromList $ map (\a -> (a, Top)) $
                              rights $ take (min 6 numargs) argLocation
          ftCO _ f = f
          
          removeBindingsTo :: Ord k => BetterifyLoc -> M.Map k (WithTop BetterifyLoc)
                           -> M.Map k (WithTop BetterifyLoc)
          removeBindingsTo x oldMap = M.mapMaybe f oldMap
              where f p@(PElem v) = if v == x then Nothing else Just p
                    f y = Just y
          
          lookupBInt64 :: BetterifyLoc -> BetterifyFact -> BetterifyLoc
          lookupBInt64 v (spills, regs)
              = case v of
                  BReg r -> case M.lookup r regs of
                              Just (PElem (BInt64 i)) -> BInt64 i
                              _ -> BReg r
                  BSpill l -> case M.lookup l spills of
                                Just (PElem (BInt64 i)) -> BInt64 i
                                _ -> BSpill l
                  _ -> v
          
          handleToR :: BetterifyLoc -> Reg -> BetterifyFact -> BetterifyFact
          handleToR v r (spills, regs)
              = ( removeBindingsTo (BReg r) spills
                , removeBindingsTo (BReg r) $ M.insert r (PElem v) regs )
              where v' = lookupBInt64 v (spills, regs) -- ?
                           
          handleToS :: BetterifyLoc -> SpillLoc -> BetterifyFact -> BetterifyFact
          handleToS v s (spills, regs)
              = ( removeBindingsTo (BSpill s) $ M.insert s (PElem v) spills
                , removeBindingsTo (BSpill s) regs )
              where v' = lookupBInt64 v (spills, regs) -- ?
          
          removeToR :: Reg -> BetterifyFact -> BetterifyFact
          removeToR r (spills, regs)
              = ( removeBindingsTo (BReg r) spills
                , M.insert r Top $ removeBindingsTo (BReg r) regs )
          
          ftOO :: Asm O O -> BetterifyFact -> BetterifyFact
          ftOO (Spill _ r s) f = handleToS (BReg r) s f
          ftOO (Reload _ s r) f = handleToR (BSpill s) r f
          ftOO (MovIRMtoR _ (IRM_I (Imm32 i)) r) f = handleToR (BInt64 $ fromIntegral i) r f
          ftOO (MovIRMtoR _ (IRM_R r0) r) f = handleToR (BReg r0) r f
          ftOO (Mov64toR _ (Imm64 i) r) f = handleToR (BInt64 i) r f
          ftOO n f = let (alive, dead) = getAliveDead n
                     in foldl (flip id) f (map removeToR dead)
          
          ftOC :: Asm O C -> BetterifyFact -> FactBase BetterifyFact
          ftOC = distributeFact
          
          rewrite :: FwdRewrite m Asm BetterifyFact
          rewrite = deepFwdRw3 rwCO rwOO rwOC
          
          rwCO :: Asm C O -> BetterifyFact -> m (Maybe (Graph Asm C O))
          rwCO n f = return Nothing
          
          getR :: Reg -> BetterifyFact -> Maybe BetterifyLoc
          getR r (spills, regs) = case M.lookup r regs of
                                    Just (PElem v) -> Just v
                                    _ -> Nothing
          
          getS :: SpillLoc -> BetterifyFact -> Maybe BetterifyLoc
          getS s (spills, regs) = case M.lookup s spills of
                                    Just (PElem v) -> Just v
                                    _ -> Nothing
          
          rwOO :: Asm O O -> BetterifyFact -> m (Maybe (Graph Asm O O))
          rwOO (Spill pos r s) f
              = return $ case getR r f of
                           Just (BReg r') -> Just $ mkMiddle $ Spill pos r' s
                           Just (BSpill s') | s == s' -> Just emptyGraph
                           _ -> Nothing
          rwOO (Reload pos s r) f
              = return $ case getS s f of
                           Just (BReg r') -> Just $ mkMiddle $ mov pos r' r
                           Just (BInt64 i) -> Just $ mkMiddle $ mov pos i r
                           Just (BSpill s')
                               | s /= s' -> Just $ mkMiddle $ Reload pos s' r
                           _ -> Nothing
          rwOO (MovIRMtoR pos (IRM_R r0) r) f
              = return $ case getR r0 f of
                           Just (BReg r0') | r0' == r -> Just emptyGraph
                                           | r0' /= r0 -> Just $ mkMiddle $ mov pos r0' r
                           Just (BInt64 i) -> Just $ mkMiddle $ mov pos i r
                           _ -> Nothing
          rwOO n f = return $ mkMiddle `fmap` mapAsm rename (const Nothing) n
              where pinned = getPinned n
                    rename r
                        | r `elem` pinned  = Nothing
                        | otherwise
                          = case getR r f of
                              Just (BReg r') | r == r' -> Nothing
                                             | otherwise -> Just r'
                              _ -> Nothing
          
          rwOC :: Asm O C -> BetterifyFact -> m (Maybe (Graph Asm O C))
          rwOC n f = return Nothing
