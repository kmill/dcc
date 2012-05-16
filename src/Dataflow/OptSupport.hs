{-# LANGUAGE GADTs, TypeSynonymInstances, TypeFamilies, RankNTypes, ScopedTypeVariables #-}
module Dataflow.OptSupport where 

import IR
import Compiler.Hoopl
import Compiler.Hoopl.Fuel
import Control.Monad
import Control.Monad.Trans
import Data.Maybe
import Data.Function

import qualified Data.Set as S


-- Useful functions

-- | Performs the cartesian product of two join functions
joinProd :: JoinFun a -> JoinFun b -> JoinFun (a, b)
joinProd fun1 fun2 l (OldFact (a1, b1)) (NewFact (a2, b2)) = (ch, (a', b'))
    where (ch1, a') = fun1 l (OldFact a1) (NewFact a2)
          (ch2, b') = fun2 l (OldFact b1) (NewFact b2)
          ch = changeIf $ SomeChange `elem` [ch1, ch2]

joinSets :: Ord a => JoinFun (S.Set a)
joinSets l (OldFact s1) (NewFact s2) = (ch, s')
    where s' = s1 `S.union` s2
          ch = changeIf $ s' `bigger` s1
          bigger = (>) `on` S.size

noLattice :: DataflowLattice ()
noLattice = DataflowLattice
            { fact_name = "no lattice"
            , fact_bot = ()
            , fact_join = const $ const $ const (NoChange, ()) }

setLattice :: Ord a => DataflowLattice (S.Set a)
setLattice = DataflowLattice
             { fact_name = "set lattice"
             , fact_bot = S.empty
             , fact_join = joinSets }

infixl 5 ><
(><) :: (a -> b -> c) -> (d -> e -> f) -> (a, d) -> (b, e) -> (c, f)
(f >< g) (a, d) (b, e) = (f a b, g d e)

          
-- see also joinMaps :: Ord k => JoinFun v -> JoinFun (Map k v)

type MaybeChange a = a -> Maybe a 
mapVE :: (VarName -> Maybe MidIRExpr) -> MaybeChange MidIRExpr
mapEE :: MaybeChange MidIRExpr -> MaybeChange MidIRExpr
mapEN :: MaybeChange MidIRExpr -> MaybeChange (MidIRInst e x) 
mapVN :: (VarName -> Maybe MidIRExpr) -> MaybeChange (MidIRInst e x)

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
mapEE f e@(Cond pos exc ext exf) =
    case (mapEE f exc, mapEE f ext, mapEE f exf) of
      (Nothing, Nothing, Nothing) -> f e
      (exc', ext', exf') -> Just $ fromMaybe e' (f e')
          where e' = Cond pos (fromMaybe exc exc')
                     (fromMaybe ext ext') (fromMaybe exf exf')

mapEN _ (Label _ _) = Nothing 
mapEN _ (PostEnter _ _) = Nothing 
mapEN _ (Enter _ _ _) = Nothing 
mapEN f (Store pos var expr) = liftM (Store pos var) $ f expr
mapEN f (DivStore pos d op num den) =
    case (f num, f den) of
      (Nothing, Nothing) -> Nothing
      (num', den') -> Just $ DivStore pos d op
                      (fromMaybe num num') (fromMaybe den den')
mapEN f (IndStore pos e1 e2) = 
    case (f e1, f e2) of 
        (Nothing, Nothing) -> Nothing 
        (e1', e2') -> Just $ IndStore pos (fromMaybe e1 e1') (fromMaybe e2 e2')
mapEN f (Call pos var str es) = 
    if all isNothing es' then Nothing 
    else Just $ Call pos var str (map (uncurry fromMaybe) (zip es es'))
        where es' = map f es
mapEN f (Callout pos var str es) = 
    if all isNothing es' then Nothing 
    else Just $ Callout pos var str (map (uncurry fromMaybe) (zip es es'))
        where es' = map f es
mapEN _ Parallel{} = Nothing
mapEN _ Branch{} = Nothing 
mapEN _ ThreadReturn{} = Nothing 
mapEN f (CondBranch pos expr tl fl) =
    case f expr of 
      Nothing -> Nothing 
      Just expr' -> Just $ CondBranch pos expr' tl fl
mapEN f (Return pos from maybeexpr) =
    case liftM f maybeexpr of 
      Nothing -> Nothing 
      Just Nothing -> Nothing 
      Just expr' -> Just $ Return pos from expr'
mapEN _ Fail{}  = Nothing
    

insnToG :: MidIRInst e x -> Graph MidIRInst e x  
insnToG n@Label{} = mkFirst n
insnToG n@PostEnter{} = mkFirst n
insnToG n@Enter{} = mkFirst n
insnToG n@Store{} = mkMiddle n 
insnToG n@DivStore{} = mkMiddle n
insnToG n@IndStore{} = mkMiddle n 
insnToG n@Call{} = mkMiddle n 
insnToG n@Callout{} = mkMiddle n 
insnToG n@Parallel{} = mkLast n
insnToG n@ThreadReturn{} = mkLast n
insnToG n@Branch{} = mkLast n 
insnToG n@CondBranch{} = mkLast n 
insnToG n@Return{} = mkLast n 
insnToG n@Fail{} = mkLast n 


fold_EE :: (a -> MidIRExpr -> a) -> a -> MidIRExpr -> a 
fold_EN :: (a -> MidIRExpr -> a) -> a -> MidIRInst e x -> a 

fold_EE f z e@(Lit _ _) = f z e 
fold_EE f z e@(Var _ _) = f z e
fold_EE f z e@(LitLabel _ _) = f z e 
fold_EE f z e@(Load _ expr) = f (fold_EE f z expr) e 
fold_EE f z e@(UnOp _ _ expr) = f (fold_EE f z expr) e
fold_EE f z e@(BinOp _ _ expr1 expr2) = f (fold_EE f (fold_EE f z expr2) expr1) e
fold_EE f z e@(Cond _ expr1 expr2 expr3) = f (fold_EE f (fold_EE f (fold_EE f z expr3) expr2) expr1) e

fold_EN _ z (Label _ _) = z
fold_EN _ z (PostEnter _ _) = z
fold_EN _ z (Enter _ _ _) = z
fold_EN f z (Store _ _ expr) = f z expr 
fold_EN f z (DivStore _ _ _ expr1 expr2) = f (f z expr2) expr1
fold_EN f z (IndStore _ expr1 expr2) = f (f z expr2) expr1
fold_EN f z (Call _ _ _ es) = foldl f z es 
fold_EN f z (Callout _ _ _ es) = foldl f z es 
fold_EN _ z (Parallel _ _ _ _ _) = z
fold_EN _ z (Branch _ _) = z
fold_EN _ z (ThreadReturn _ _) = z
fold_EN f z (CondBranch _ expr _ _) = f z expr 
fold_EN _ z (Return _ from Nothing) = z
fold_EN f z (Return _ from (Just expr)) = f z expr
fold_EN _ z (Fail _) = z




-- Alive Dead Information 


type MidAliveDead = Maybe ([VarName], [VarName])

--infixl 5 <+>

--(<+>) :: MidAliveDead -> MidAliveDead -> MidAliveDead 
--(a1,d1) <+> (a2,d2) = (a1++a2, d1++d2)

emptyMAD :: MidAliveDead
emptyMAD = Just ([], [])

-- | Gets the variables which are used and fefined (also known as 
-- "alive" and "dead", respectively, because of backwards liveness 
-- analysis). 

getMidAliveDead :: MidIRInst e x -> MidAliveDead
getMidAliveDead inst 
    = case inst of 
        Label _ _ -> emptyMAD 
        Enter _ _ args -> Just ([], args)
        PostEnter _ _ -> emptyMAD 
        n@(Store _ x _) -> Just (S.toList $ getUses S.empty n, [x])
        n@(DivStore _ x _ _ _) -> Just (S.toList $ getUses S.empty n, [x])
        n@(IndStore _ _ _) -> Just (S.toList $ getUses S.empty n, [])
        n@(Call _ x _ _) -> Just (S.toList $ getUses S.empty n, [x])
        n@(Callout _ x _ _) -> Just (S.toList $ getUses S.empty n, [x])
        n@(Parallel _ _ x _ _) -> Just ([], [x])
        ThreadReturn _ _ -> Nothing
        Branch _ _ -> emptyMAD
        n@(CondBranch _ _ _ _) -> Just (S.toList $ getUses S.empty n, [])
        n@(Return _ _ _) -> Just (S.toList $ getUses S.empty n, [])
        Fail _ -> emptyMAD

      where getUses :: S.Set VarName -> MidIRInst e x -> S.Set VarName
            getUses = fold_EN (fold_EE addVar) 
            addVar s (Var _ v) = S.insert v s 
            addVar s _ = s 
