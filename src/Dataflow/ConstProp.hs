{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}

module Dataflow.ConstProp where

import Control.Monad
import qualified Data.Map as Map

import Compiler.Hoopl
import IR2
import AST(SourcePos)
import Data.Int
import Data.Maybe 

type LitVal = (SourcePos, Int64)

type Node = MidIRInst 

-- Type and definition of the lattice
-- Need to figure out what "Var" Corresponds to 
type ConstFact = Map.Map VarName (WithTop LitVal)
constLattice :: DataflowLattice ConstFact
constLattice = DataflowLattice { fact_name = "Constant Propagation Lattice (Arhrhrhghg)"
                               , fact_bot = Map.empty 
                               , fact_join = joinMaps (extendJoinDomain constFactAdd) }
    where constFactAdd _ (OldFact old) (NewFact new) = if new == old then (NoChange, PElem new)
                                                       else (SomeChange, Top)

initFact :: [VarName] -> ConstFact 
initFact vars = Map.fromList $ [(v, Top) | v <- vars]

emptyFact :: ConstFact 
emptyFact = fact_bot constLattice

-- Analysis: variable equals a literal constant
varHasLit :: FwdTransfer Node ConstFact
varHasLit = mkFTransfer ft
    where
      ft :: MidIRInst e x -> ConstFact -> Fact x ConstFact
      ft (Label _ _) f = f
      ft (Enter _ _ _) f = f
      ft (Store _ x (Lit pos k)) f = Map.insert x (PElem (pos, k)) f
      ft (Store _ x _) f = Map.insert x Top f
      ft (CondStore _ x _ _)  f = Map.insert x Top f 
      ft (IndStore _ _ _) f = f
      ft (Spill _ _ _) f = f
      ft (UnSpill _ x _) f = Map.insert x Top f 
      ft (Call _ _ _ _) f = f
      ft (Callout _ _ _ _) f = f
      ft (Branch _ l) f = mapSingleton l f
      ft (CondBranch _ (Var pos x) tl fl) f 
          = mkFactBase constLattice [ (tl, Map.insert x (PElem (pos, -1)) f)
                                    , (fl, Map.insert x (PElem (pos, 0)) f) ]
      ft (CondBranch _ _ tl fl) f 
          = mkFactBase constLattice [ (tl, f)
                                    , (fl, f) ]
      ft (Return _ _) f = mapEmpty
      ft (Fail _) f = mapEmpty

varHasLit' :: FwdTransfer Node ConstFact 
varHasLit' = mkFTransfer ft 
    where 
      ft :: MidIRInst e x -> ConstFact -> Fact x ConstFact
      ft (Label _ _) f = f
      ft (Enter _ _ _) f = f
      ft (Store _ x (Lit pos k)) f = f
      ft (Store _ x _) f = f
      ft (CondStore _ x _ _)  f =f
      ft (IndStore _ _ _) f = f
      ft (Spill _ _ _) f = f
      ft (UnSpill _ x _) f =f
      ft (Call _ _ _ _) f = f
      ft (Callout _ _ _ _) f = f
      ft (Branch _ l) f = mapEmpty
      ft (CondBranch _ (Var pos x) tl fl) f 
          = mapEmpty
      ft (CondBranch _ _ tl fl) f 
          = mapEmpty
      ft (Return _ _) f = mapEmpty
      ft (Fail _) f = mapEmpty


-- Rewrite function: replace constant variables
constProp :: forall m. FuelMonad m => FwdRewrite m Node ConstFact
constProp = mkFRewrite cp 
    where 
      cp :: Node e x -> ConstFact -> m (Maybe (Graph Node e x))
      cp node f 
             = return $ liftM insnToG $ mapVN (lookup f) node
      lookup :: ConstFact -> VarName -> Maybe MidIRExpr
      lookup f x = case Map.lookup x f of 
                     Just (PElem (pos, v)) -> Just $ Lit pos v
                     _ -> Nothing

simplify :: forall m f . FuelMonad m => FwdRewrite m Node f
simplify = deepFwdRw simp 
    where 
      simp :: forall e x. Node e x -> f -> m (Maybe (Graph Node e x))
      simp node _ = return $ liftM insnToG $ s_node node 
      s_node :: Node e x -> Maybe (Node e x)
      s_node (CondBranch pos (Lit _ x) tl fl) 
          = Just $ Branch pos (if intToBool x then tl else fl)
      s_node n = (mapEN . mapEE) s_exp n 
      s_exp (BinOp pos op (Lit _ x1) (Lit _ x2)) 
          = Just $ Lit pos $ (binOp op) x1 x2
      s_exp (UnOp pos op (Lit _ x))
          = Just $ Lit pos $ (unOp op) x
      s_exp _ = Nothing
      binOp OpAdd = (+)
      binOp OpSub = (-)
      binOp OpMul = (*)
      binOp OpDiv = div
      binOp OpMod = rem
      binOp CmpLT = \x y -> boolToInt $ x < y
      binOp CmpGT = \x y -> boolToInt $ x > y 
      binOp CmpLTE = \x y -> boolToInt $ x <= y 
      binOp CmpGTE = \x y -> boolToInt $ x >= y 
      binOp CmpEQ = \x y -> boolToInt $ x == y 
      binOp CmpNEQ = \x y -> boolToInt $ x /= y
      unOp OpNeg = negate 
      unOp OpNot = boolToInt . not . intToBool


type MaybeChange a = a -> Maybe a 
mapVE :: (VarName -> Maybe MidIRExpr) -> MaybeChange MidIRExpr
mapEE :: MaybeChange MidIRExpr -> MaybeChange MidIRExpr
mapEN :: MaybeChange MidIRExpr -> MaybeChange (Node e x) 
mapVN :: (VarName -> Maybe MidIRExpr) -> MaybeChange (Node e x)

mapVN = mapEN . mapEE . mapVE

mapVE f (Var _ v) = f v 
mapVE _ _ = Nothing

mapEE f e@(Lit _ _) = f e 
mapEE f e@(Var _ _) = f e 
mapEE f e@(LitLabel _ _) = f e 
mapEE f e@(Load pos expr) = 
    case mapEE f expr of 
      Just expr' -> Just $ fromMaybe e' (f e')
                      where e' = Load pos expr'
      Nothing -> f e 
mapEE f e@(UnOp pos op expr) = 
    case mapEE f expr of 
      Nothing -> f e
      Just expr' -> Just $ fromMaybe e' (f e')
          where e' = UnOp pos op expr'
mapEE f e@(BinOp pos op e1 e2) = 
    case (mapEE f e1, mapEE f e2) of 
      (Nothing, Nothing) -> f e 
      (e1', e2') -> Just $ fromMaybe e' (f e')
          where e' = BinOp pos op (fromMaybe e1 e1') (fromMaybe e2 e2')

mapEN _ (Label _ _) = Nothing 
mapEN _ (Enter _ _ _) = Nothing 
mapEN f (Store pos var expr) = liftM (Store pos var) $ f expr
mapEN f (CondStore pos var e1 e2) =
    case (f e1, f e2) of 
        (Nothing, Nothing) -> Nothing
        (e1', e2') -> Just $ CondStore pos var (fromMaybe e1 e1') (fromMaybe e2 e2')
mapEN f (IndStore pos e1 e2) = 
    case (f e1, f e2) of 
        (Nothing, Nothing) -> Nothing 
        (e1', e2') -> Just $ IndStore pos (fromMaybe e1 e1') (fromMaybe e2 e2')
mapEN _ (Spill _ _ _) = Nothing 
mapEN _ (UnSpill _ _ _) = Nothing 
mapEN f (Call pos var str es) = 
    if all isNothing es' then Nothing 
    else Just $ Call pos var str (map (uncurry fromMaybe) (zip es es'))
        where es' = map f es
mapEN f (Callout pos var str es) = 
    if all isNothing es' then Nothing 
    else Just $ Callout pos var str (map (uncurry fromMaybe) (zip es es'))
        where es' = map f es
mapEN _ (Branch _ _) = Nothing 
mapEN f (CondBranch pos expr tl fl) =
    case f expr of 
      Nothing -> Nothing 
      Just expr' -> Just $ CondBranch pos expr' tl fl
mapEN f (Return pos maybeexpr) =
    case liftM f maybeexpr of 
      Nothing -> Nothing 
      Just Nothing -> Nothing 
      Just expr' -> Just $ Return pos expr'
mapEN _ (Fail _)  = Nothing
    

insnToG :: Node e x -> Graph Node e x  
insnToG n@(Label _ _) = mkFirst n
insnToG n@(Enter _ _ _) = mkFirst n
insnToG n@(Store _ _ _) = mkMiddle n 
insnToG n@(CondStore _ _ _ _) = mkMiddle n 
insnToG n@(IndStore _ _ _) = mkMiddle n 
insnToG n@(Spill _ _ _) = mkMiddle n 
insnToG n@(UnSpill _ _ _) = mkMiddle n 
insnToG n@(Call _ _ _ _) = mkMiddle n 
insnToG n@(Callout _ _ _ _) = mkMiddle n 
insnToG n@(Branch _ _) = mkLast n 
insnToG n@(CondBranch _ _ _ _) = mkLast n 
insnToG n@(Return _ _) = mkLast n 
insnToG n@(Fail _) = mkLast n 