{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-} 

module Dataflow.Dominator where 

import qualified Data.Set as S 

import Compiler.Hoopl 
import IR 
import Dataflow.OptSupport 



type DominFact = WithBot (S.Set Label)
dominatorLattice :: DataflowLattice DominFact 
dominatorLattice = DataflowLattice { fact_name = "Dominator Lattice" 
                                   , fact_bot = Bot
                                   , fact_join = intersectMaps }
    where intersectMaps :: Label -> OldFact DominFact -> NewFact DominFact -> (ChangeFlag, DominFact)
          intersectMaps _ (OldFact old) (NewFact new) 
              = case (old, new) of 
                  (old', Bot) -> (NoChange, old')
                  (Bot, new') -> (SomeChange, new')
                  (PElem oldSet, PElem newSet) -> (ch, PElem j)
                      where j = S.intersection oldSet newSet 
                            ch = changeIf (S.size j /= S.size oldSet)

dominatorAnalysis :: FwdTransfer MidIRInst DominFact 
dominatorAnalysis = mkFTransfer ft 
    where ft :: MidIRInst e x -> DominFact -> Fact x DominFact 
          ft (Label _ l) f = insertLabel l f
          ft (PostEnter _ l) f = insertLabel l f
          ft (Enter _ l _) f = insertLabel l f 
          ft (Store _ _ _) f = f
          ft (DivStore _ _ _ _ _) f = f
          ft (IndStore _ _ _) f = f
          ft (Call _ _ _ _) f = f
          ft (Callout _ _ _ _) f = f
          ft (Branch _ l) f = mapSingleton l $ insertLabel l f 
          ft (CondBranch _ _ tl fl) f 
              = mkFactBase dominatorLattice [ (tl, insertLabel tl f) 
                                            , (fl, insertLabel fl f) ]
          ft (Return _ _ _) f = mapEmpty 
          ft (Fail _) f = mapEmpty

          insertLabel :: Label -> DominFact -> DominFact
          insertLabel l Bot = PElem $ S.singleton l 
          insertLabel l (PElem s) = PElem $ S.insert l s


generalDominAnalysis :: (NonLocal n) => FwdTransfer n DominFact 
generalDominAnalysis = mkFTransfer3 ftBegin ftMiddle ftEnd 
    where ftBegin :: (NonLocal n) => n C O -> DominFact -> DominFact 
          ftBegin inst f = insertLabel (entryLabel inst) f 

          ftMiddle :: (NonLocal n) => n O O -> DominFact -> DominFact 
          ftMiddle inst f = f 

          ftEnd :: (NonLocal n) => n O C -> DominFact -> FactBase DominFact
          ftEnd inst f = mkFactBase dominatorLattice [ (l, insertLabel l f) | l <- successors inst]

          insertLabel :: Label -> DominFact -> DominFact
          insertLabel l Bot = PElem $ S.singleton l 
          insertLabel l (PElem s) = PElem $ S.insert l s
                
