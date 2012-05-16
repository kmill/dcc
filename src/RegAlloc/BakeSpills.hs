{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

-- | Bakes spills into being moves
module RegAlloc.BakeSpills(performBakeSpills) where

import CLI
import qualified Data.Set as S
import Data.Int
import Data.Maybe
import Data.List
import DataflowTypes
import Dataflow.OptSupport
import qualified IR as I
import Assembly
import Compiler.Hoopl
import Debug.Trace

performBakeSpills :: (CheckpointMonad m, FuelMonad m)
                     => CompilerOpts -> LowIRRepr -> m LowIRRepr
performBakeSpills opts asm
    = do (graph', ipcs) <- collectSpills opts mlabels graph
         return $ asm { lowIRGraph = graph' 
                      , lowIRIPCSize = 8*ipcs }
      where graph = lowIRGraph asm
            mlabels = (map I.methodEntry $ lowIRMethods asm)

-- | Collects and rewrites the spills in the graph to moves.
collectSpills :: (CheckpointMonad m, FuelMonad m)
                 => CompilerOpts -> [Label] -> Graph Asm C C -> m (Graph Asm C C, Int)
collectSpills opts mlabels graph
    = do (_, f, _) <- analyzeAndRewriteBwd
                      collectSpillPass
                      (JustC mlabels)
                      graph
                      mapEmpty
         (g, _, _) <- analyzeAndRewriteFwd
                      (rewriteSpillPass opts f)
                      (JustC mlabels)
                      graph
                      f
         let spills = S.unions $ map (\l -> fromJust $ lookupFact l f) mlabels
             ipcSpills = filter isIPC $ S.toList spills
         return (g, length ipcSpills)

isIPC (SpillIPC _) = True
isIPC _ = False
 
 -- | Gets the list of spills for each entry point. TODO: make it also
-- find live ranges for spills so we can reuse stack space.
collectSpillPass :: (CheckpointMonad m, FuelMonad m)
                    => BwdPass m Asm (S.Set SpillLoc)
collectSpillPass = BwdPass
                   { bp_lattice = setLattice
                   , bp_transfer = getSpillTransfer
                   , bp_rewrite = noBwdRewrite }
    where
      getSpillTransfer :: BwdTransfer Asm (S.Set SpillLoc)
      getSpillTransfer = mkBTransfer3 usedCO usedOO usedOC
          where
            usedCO :: Asm C O -> (S.Set SpillLoc) -> (S.Set SpillLoc)
            usedCO _ f = f

            usedOO :: Asm O O -> (S.Set SpillLoc) -> (S.Set SpillLoc)
            usedOO (Spill _ _ s) f = S.insert s f
            usedOO (Reload _ s _) f = S.insert s f
            usedOO _ f = f

            usedOC :: Asm O C -> FactBase (S.Set SpillLoc) -> (S.Set SpillLoc)
            usedOC (InternalFunc _ fl (Imm32BlockLabel el 0)) f
                = S.unions [ S.filter isIPC (fromMaybe S.empty $ lookupFact fl f)
                           , fromMaybe S.empty $ lookupFact el f ] 
            usedOC x f = S.unions $ map
                         ((fromMaybe S.empty) . (flip lookupFact f))
                         (successors x)


-- | Rewrites the spills to moves.
rewriteSpillPass :: (CheckpointMonad m, FuelMonad m) =>
                    CompilerOpts -> FactBase (S.Set SpillLoc)
                    -> FwdPass m Asm (S.Set SpillLoc)
rewriteSpillPass opts fb = FwdPass 
                           { fp_lattice = rwLattice
                           , fp_transfer = sTransfer
                           , fp_rewrite = rewriteSpill }
    where rwLattice :: DataflowLattice (S.Set SpillLoc)
          rwLattice = setLattice
          
          sTransfer :: FwdTransfer Asm (S.Set SpillLoc)
          sTransfer = mkFTransfer3 g g' g''
              where 
                g :: Asm C O -> S.Set SpillLoc -> S.Set SpillLoc
                g (Enter p l _ _) _ = let f = fromMaybe S.empty (lookupFact l fb)
                                      in f
                g e f = f
                g' e f = f
                g'' :: Asm O C -> S.Set SpillLoc -> FactBase (S.Set SpillLoc)
                g'' (InternalFunc _ fl (Imm32BlockLabel el 0)) f
                  = mkFactBase rwLattice $ [(el, f), (fl, S.empty)]
                g'' e f = mkFactBase rwLattice $ zip (successors e) (repeat f)

          rewriteSpill :: forall m. FuelMonad m => FwdRewrite m Asm (S.Set SpillLoc)
          rewriteSpill = mkFRewrite d
              where 
                d :: Asm e x -> S.Set SpillLoc -> m (Maybe (Graph Asm e x))
                d (Spill pos reg s) f
                    = return $ Just $ mkMiddle $ mov pos reg (toMem s f)
                d (Reload pos s reg) f
                    = return $ Just $ mkMiddle $ mov pos (toMem s f) reg
                d (Enter pos l n x) f = if x' == x
                                        then return Nothing
                                        else return $ Just $ mkFirst $
                                             Enter pos l n x'
                    where x' = countSpillID f
                d (Leave pos rets x) f = if x' == x
                                         then return Nothing
                                         else (let inst = Leave pos rets x'
                                               in return $ Just $ mkLast inst)
                    where x' = countSpillID f

                d _ f = return Nothing
                
                countSpillID f = toNearestSafeSP $ fromIntegral $
                                 8 * (length $ normalSpills f)
                normalSpills f = S.toList $ S.filter (\s -> case s of
                                                              SpillArg _ -> False
                                                              SpillID _ -> True
                                                              SpillSID _ -> True
                                                              SpillIPC _ -> False) f

                toMem :: SpillLoc -> S.Set SpillLoc -> MemAddr
                toMem (SpillArg r) f = MemAddr (Just $ MReg RSP)
                                       (Imm32 $ 8*(fromIntegral r) + 8 + countSpillID f)
                                       Nothing SOne
                toMem (SpillIPC i) f = MemAddr Nothing
                                       (Imm32Label "main_ipc" $ 8 * (fromIntegral i))
                                       Nothing SOne
                toMem sl f = MemAddr (Just $ MReg RSP)
                             (Imm32 $ fromIntegral (8 * fromJust (findIndex (==sl) $ normalSpills f)))
                             Nothing SOne
                
                toNearestSafeSP :: Int32 -> Int32
                toNearestSafeSP i = if macMode opts 
                                    then i + ((i+8) `rem` (8*2))
                                    else i

