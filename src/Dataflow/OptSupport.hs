{-# LANGUAGE GADTs #-}
module Dataflow.OptSupport where 

import IR
import Compiler.Hoopl
import Control.Monad
import Data.Maybe

-- Useful functions 


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
mapEN _ (Branch _ _) = Nothing 
mapEN f (CondBranch pos expr tl fl) =
    case f expr of 
      Nothing -> Nothing 
      Just expr' -> Just $ CondBranch pos expr' tl fl
mapEN f (Return pos from maybeexpr) =
    case liftM f maybeexpr of 
      Nothing -> Nothing 
      Just Nothing -> Nothing 
      Just expr' -> Just $ Return pos from expr'
mapEN _ (Fail _)  = Nothing
    

insnToG :: MidIRInst e x -> Graph MidIRInst e x  
insnToG n@(Label _ _) = mkFirst n
insnToG n@(PostEnter _ _) = mkFirst n
insnToG n@(Enter _ _ _) = mkFirst n
insnToG n@(Store _ _ _) = mkMiddle n 
insnToG n@(IndStore _ _ _) = mkMiddle n 
insnToG n@(Call _ _ _ _) = mkMiddle n 
insnToG n@(Callout _ _ _ _) = mkMiddle n 
insnToG n@(Branch _ _) = mkLast n 
insnToG n@(CondBranch _ _ _ _) = mkLast n 
insnToG n@(Return _ _ _) = mkLast n 
insnToG n@(Fail _) = mkLast n 


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
fold_EN f z (IndStore _ expr1 expr2) = f (f z expr2) expr1
fold_EN f z (Call _ _ _ es) = foldl f z es 
fold_EN f z (Callout _ _ _ es) = foldl f z es 
fold_EN _ z (Branch _ _) = z
fold_EN f z (CondBranch _ expr _ _) = f z expr 
fold_EN _ z (Return _ from Nothing) = z
fold_EN f z (Return _ from (Just expr)) = f z expr
fold_EN _ z (Fail _) = z