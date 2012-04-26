{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}
module Dataflow.LICM where

import Dataflow.OptSupport
import AST(SourcePos)
import Compiler.Hoopl
import IR
import qualified Data.Set as S
import Data.Maybe(catMaybes)

data (Ord v) => SInst v
    = SStore SourcePos v (Expr v)
    | SDivStore SourcePos v DivOp (Expr v) (Expr v)
    | SIndStore SourcePos (Expr v) (Expr v)
    | SOtherInst
      deriving (Eq, Ord)

storeInst :: (Ord v) => Inst v e x -> SInst v
storeInst (Store pos var expr) = SStore pos var expr
storeInst (DivStore pos var op expr1 expr2) = SDivStore pos var op expr1 expr2
storeInst (IndStore pos dest src) = SIndStore pos dest src
storeInst _ = SOtherInst

unStoreInst :: (Ord v) => SInst v -> Maybe (Inst v O O)
unStoreInst (SStore pos var expr) = Just $ Store pos var expr
unStoreInst (SDivStore pos var op expr1 expr2) = Just $ DivStore pos var op expr1 expr2
unStoreInst (SIndStore pos dest src) = Just $ IndStore pos dest src
unStoreInst SOtherInst = Nothing

type MSInst = SInst VarName

-- Set of instructions which can be moved to this point
type MotionFact = S.Set MSInst
motionLattice :: DataflowLattice MotionFact
motionLattice = DataflowLattice { fact_name = "Code Motion Lattice"
                                , fact_bot = S.empty
                                , fact_join = intersectMaps }
    where intersectMaps :: Label -> OldFact MotionFact -> NewFact MotionFact -> (ChangeFlag, MotionFact)
          intersectMaps _ (OldFact oldSet) (NewFact newSet)
              = (c, res)
              where c = SomeChange
                    res = S.intersection newSet oldSet

emptyMotionFact :: MotionFact
emptyMotionFact = S.empty

exprDepend :: (Ord v) => Expr v -> S.Set v
exprDepend (Var _ v) = S.singleton v
exprDepend (Load _ expr) = exprDepend expr
exprDepend (UnOp _ _ expr) = exprDepend expr
exprDepend (BinOp _ _ expr1 expr2) = S.unions $ map exprDepend $ [expr1, expr2] 
exprDepend (Cond _ exprc expr1 expr2)
    = S.unions $ map exprDepend $ [exprc, expr1, expr2]
exprDepend _ = S.empty

instDepend :: (Ord v) => SInst v -> S.Set v
instDepend (SStore _ _ expr) = exprDepend expr
instDepend (SDivStore _ _ _ expr1 expr2) = S.unions $ map exprDepend $ [expr1, expr2]
instDepend (SIndStore _ expr1 expr2) = S.unions $ map exprDepend $ [expr1, expr2]
instDepend SOtherInst = S.empty

motionTransfer :: BwdTransfer MidIRInst MotionFact
motionTransfer = mkBTransfer3 btCO btOO btOC
    where btCO :: MidIRInst C O -> MotionFact -> MotionFact
          btCO i@(Enter _ _ args) f = addDefinitions args f
          btCO _ f = f

          btOO :: MidIRInst O O -> MotionFact -> MotionFact
          btOO i@(Store _ var expr) f
              = addDefinition var (S.insert (storeInst i) f)
          btOO i@(DivStore _ var _ expr1 expr2) f
              = addDefinition var (S.insert (storeInst i) f)
          btOO i@(IndStore _ _ _) f = S.insert (storeInst i) f
          btOO (Call _ var _ _) f = addDefinition var f
          btOO (Callout _ var _ _) f = addDefinition var f

          btOC :: MidIRInst O C -> FactBase MotionFact -> MotionFact
          btOC _ = S.unions . mapElems

          addDefinition :: VarName -> MotionFact -> MotionFact
          addDefinition var fact = S.filter (not . dependsOn var) fact'
              where fact'
                        | killIndStores = S.filter (not . isIndStore) fact
                        | otherwise = fact
                    killIndStores = S.null $ S.filter (dependsOn var) indStores
                    indStores = S.filter isIndStore fact
                    dependsOn :: VarName -> MSInst -> Bool
                    dependsOn var = S.member var . instDepend
                    isIndStore SIndStore{} = True
                    isIndStore _ = False
          addDefinitions :: [VarName] -> MotionFact -> MotionFact
          addDefinitions vars initial = foldr addDefinition initial vars

motionRewrite :: forall m . FuelMonad m => BwdRewrite m MidIRInst MotionFact
motionRewrite = mkBRewrite3 (\i _ -> return $ Just $ mkFirst i) (\i _ -> return $ Just $ mkMiddle i) r
    where r :: MidIRInst O C -> Fact C MotionFact -> m (Maybe (Graph MidIRInst O C))
          r inst facts = return $ Just ((mkMiddles $ getInstrs facts) <*> (mkLast inst))
          getInstrs :: FactBase MotionFact -> [MidIRInst O O]
          getInstrs = catMaybes . map unStoreInst . S.toList . S.unions . mapElems
