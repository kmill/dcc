{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Dataflow.BlockElimAsm where 

import Compiler.Hoopl
import Assembly
import Control.Monad
import Data.Maybe
import Debug.Trace
import qualified IR as I

type LastLabel = Maybe Label

performBlockElimAsm :: (CheckpointMonad m, FuelMonad m) => LowIRRepr -> m LowIRRepr
performBlockElimAsm asm
    = do graph' <- performBlockElimAsm' mlabels graph
         return $ asm { lowIRGraph = graph' }
      where graph = lowIRGraph asm
            mlabels = (map I.methodEntry $ lowIRMethods asm)

performBlockElimAsm' :: (CheckpointMonad m, FuelMonad m) => 
                       [Label] -> Graph Asm C C -> m (Graph Asm C C)
performBlockElimAsm' mlabels graph
    = do (graph', factBase, _) <- analyzeAndRewriteBwd
                                  blockElimPass
                                  (JustC mlabels)
                                  graph
                                  (mapFromList (map (\l -> (l, fact_bot lastLabelLattice)) mlabels))
         return graph'
         
blockElimPass :: (CheckpointMonad m, FuelMonad m) => BwdPass m Asm LastLabel
blockElimPass = BwdPass 
                { bp_lattice = lastLabelLattice
                , bp_transfer = lastLabelness
                , bp_rewrite = lastLabelElim }

lastLabelLattice :: DataflowLattice LastLabel
lastLabelLattice = DataflowLattice { fact_name = "Last Labels"
                                   , fact_bot = Nothing
                                   , fact_join = add
                                   }
  where add _ (OldFact o) (NewFact n) = (c, n)
          where c = changeIf (o /= n)

lastLabelness :: BwdTransfer Asm LastLabel
lastLabelness = mkBTransfer f
  where f :: Asm e x -> Fact x LastLabel -> LastLabel
        f (Jmp _ (Imm32BlockLabel l 0)) k = 
          case lookupFact l k of
            Just l' -> l' `mplus` Just l
            Nothing -> Just l
        f (Jmp _ _) k = Nothing
        f (Label _ l) (Just l')
            | l == l'  = Nothing
            | otherwise = Just l'
        f (Label _ l) Nothing = Nothing
        f (Enter _ _ _ _) k = Nothing
        
        f _ _ = Nothing

--Special case of fromJust for Branch, since it could be removed in the previous transfer.
lastLabelElim :: forall m . FuelMonad m => BwdRewrite m Asm LastLabel
lastLabelElim = deepBwdRw ll
  where
    ll :: Asm e x -> Fact x LastLabel -> m (Maybe (Graph Asm e x))
    ll (Jmp p (Imm32BlockLabel l 0)) f = 
      return $ case lookupFact l f of
          Nothing -> Nothing
          Just mm -> mm >>= (Just . mkLast . (\l' -> Jmp p (Imm32BlockLabel l' 0)))
    ll (JCond p flag (Imm32BlockLabel tl 0) fl) f
        | tl == fl = return $ Just $ mkLast $ Jmp p (Imm32BlockLabel tl 0)
        | otherwise =
            return $ do tl' <- fun tl
                        fl' <- fun fl
                        guard $ [tl', fl'] /= [tl, fl]
                        Just $ mkLast $ JCond p flag (Imm32BlockLabel tl' 0) fl'
        where
          fun :: Label -> Maybe Label
          --fun l = fromJust (lookupFact l f) `mplus` (Just l)
          fun l = fromMaybe (Just l) (lookupFact l f) `mplus` (Just l)
--    ll (Enter p l args) (Just l')
--        = return $ Just (mkFirst (Enter p l args)
--                         <*> mkLast (Branch p l'))
    ll _ f = return Nothing
