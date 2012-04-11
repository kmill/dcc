{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}

-- | It is imperative to justify all rules put into the simplifier.
-- For instance, you can't negate the most negative integer safely!

module AlgSimplify(algSimplifyInst) where

import IR
import Control.Monad
import Data.Int
import Data.Maybe
import Data.List
import AST(SourcePos)
import Debug.Trace

algSimplifyInst :: forall v e x. (Show v, Ord v)
                   => Inst v e x -> Maybe (Inst v e x)
algSimplifyInst e = runAM $ simpI e

--algSimplifyExpr :: (Show v, Ord v) => Expr v -> Expr v
--algSimplifyExpr e = case runAM $ simpE e of
--                      Just e' -> e'
--                      Nothing -> error ("couldn't simplify " ++ show e)

-- | algebraic simplification monad.  It's just Maybe.  We're doing it
-- explicitly in the event we need more information (like error
-- handling).
data AM a = AM { runAM :: Maybe a }

instance Monad AM where
    return a = AM $ Just a
    ma >>= f = AM $ runAM ma >>= (runAM . f)
    fail _ = AM $ Nothing

instance Functor AM where
    fmap f ma = f `fmap` ma

instance MonadPlus AM where
    mzero = AM Nothing
    ma `mplus` mb = AM $ runAM ma `mplus` runAM mb

simpI :: forall v e x. (Show v, Ord v) => Inst v e x -> AM (Inst v e x)
simpI e = case e of
            Store pos v exp ->
                do exp' <- simpE exp
                   return $ Store pos v exp'
            IndStore pos dexp sexp ->
                do [dexp', sexp'] <- simpEMany [dexp, sexp]
                   return $ IndStore pos dexp' sexp'
            Call pos v name exprs ->
                do exprs' <- simpEMany exprs
                   return $ Call pos v name exprs'
            Callout pos v name exprs ->
                do exprs' <- simpEMany exprs
                   return $ Callout pos v name exprs'
            CondBranch pos exp tl fl ->
                do exp' <- simpE exp
                   case exp' of
                     Lit _ x ->
                         return $ Branch pos
                                    $ if intToBool x then tl else fl
                     _ -> mzero
            Return pos (Just exp) ->
                do exp' <- simpE exp
                   return $ Return pos (Just exp')
            _ -> mzero

-- | Here to make rules look nicer.  Just return.
withExpr :: Expr v -> AM (Expr v)
withExpr = return

-- | Makes simpE always succeed by making the result be 'e' on
-- failure.
simpES :: (Show v, Ord v) => Expr v -> AM (Expr v)
simpES e = simpE e `mplus` return e

--case runAM $ simpE e of
--             Just e' -> return e'
--             _ -> return e

-- | Runs simpEM but wraps the result in Just.
--simpEM' :: (Show v, Ord v) => Expr v -> AM (Maybe (Expr v))
--simpEM' e = traceM ("em'",e) $ (simpE e `mplus` (return $ Just e))

simpEMany :: (Show v, Ord v) => [Expr v] -> AM [Expr v]
simpEMany es = let es' = map (runAM . simpE) es
               in do guard $ not $ null (catMaybes es')
                     return [fromMaybe e e' | (e,e') <- zip es es']

simpE :: (Show v, Ord v) => Expr v -> AM (Expr v)
simpE e = traceM ("simpE", e) $ msum rules
    where
      rules =
          [ do Lit _ _ <- withExpr e
               mzero -- nothing to simplify
          , do Var _ _ <- withExpr e
               mzero -- nothing to simplify
          , do LitLabel _ _ <- withExpr e
               mzero -- nothing to simplify
          , do Load pos le <- withExpr e
               sle <- simpE le
               return $ Load pos sle
          , do UnOp pos op ex <- withExpr e
               sex <- simpE ex
               simpES $ UnOp pos op sex
          , do UnOp pos op ex <- withExpr e
               -- ex is simplified by previous rule
               simpUnOp pos op ex
          , do BinOp pos op ex1 ex2 <- withExpr e
               [sex1, sex2] <- simpEMany [ex1, ex2]
               simpES $ BinOp pos op sex1 sex2
          , do BinOp pos op ex1 ex2 <- withExpr e
               -- ex1 and ex2 are simplified by previous rule
               simpBinOp pos op ex1 ex2
          , do Cond pos cex tex fex <- withExpr e
               [scex, stex, sfex] <- simpEMany [cex, tex, fex]
               case scex of
                 Lit _ x ->
                     return $ if intToBool x then stex else sfex
                 _ ->
                     return $ Cond pos scex stex sfex
          ]

flattenOp :: Ord v => BinOp -> Expr v -> [Expr v]
flattenOp op e@(BinOp _ op' e1 e2)
    | op == op'  = flattenOp op e1 ++ flattenOp op e2
    | otherwise  = [e]
flattenOp op e = [e]

simpUnOp :: Ord v => SourcePos -> UnOp -> Expr v -> AM (Expr v)
simpUnOp pos op sex = msum rules
    where
      rules =
          [ do guard $ op == OpNot
               Lit litpos i <- withExpr sex
               return $ Lit pos (unOp op i)
          , do guard $ op == OpNeg
               Lit litpos i <- withExpr sex
               guard $ i /= minBound
               return $ Lit pos (unOp op i)
          -- Don't put in a default case.
          ]

traceM :: (Show a, Show b) => b -> AM a -> AM a
traceM x a = a

traceM' :: (Show a, Show b) => b -> AM a -> AM a
traceM' x ma = do a <- trace ("start: " ++ show x) ma
                  trace ("monad value: "++show a ++ "; " ++show x) $ return a
               `mplus` trace ("fail: " ++ show x) mzero

simpBinOp :: (Show v, Ord v) => SourcePos -> BinOp -> Expr v -> Expr v
          -> AM (Expr v)
simpBinOp pos op sex1 sex2 = traceM ("bin", op, sex1, sex2) $ msum rules
    where
      rules =
          [ -- This rule does constant folding if both sides are
            -- constants. unless there is a divide by zero.
            do Lit _ i1 <- withExpr sex1
               Lit _ i2 <- withExpr sex2
               guard $ (op /= OpDiv) || (i2 /= 0)
               guard $ (op /= OpMod) || (i2 /= 0)
               return $ Lit pos (binOp op i1 i2)
          -- The following rule enforces the order that literals occur
          -- at the beginning of a sequence of
          -- additions or multiplications
          , do guard $ op `elem` [OpAdd, OpMul]
               guard $ sex1 > sex2
               simpES $ BinOp pos op sex2 sex1
          -- Reassociates left-association to right-association for
          -- addition and multiplication
          , do guard $ op `elem` [OpAdd, OpMul]
               BinOp _ op' oper1 oper2 <- withExpr sex1
               guard $ op' == op
               guard $ oper2 > sex2
               let [a, b, c] = sort [oper1, oper2, sex2]
               oper1' <- simpES $ BinOp pos op a b
               simpES $ BinOp pos op oper1' c
          , do Lit _ i1 <- withExpr sex2
               guard $ op `elem` [OpAdd, OpMul]
               BinOp _ op' oper1 (Lit litpos i2) <- withExpr sex1
               guard $ op' == op
               simpES $ BinOp pos op oper1
                          (Lit litpos (binOp op i1 i2))
          -- If we are adding zero, we can safely not add the zero
          , do guard $ op == OpAdd
               Lit _ 0 <- withExpr sex1
               return $ sex2
          -- If we are subtracting from zero, we can do a negation.
          , do guard $ op == OpSub
               Lit _ 0 <- withExpr sex1
               simpES $ UnOp pos OpNeg sex2
          -- If we are subtracting a zero, we can just not do that.
          , do guard $ op == OpSub
               Lit _ 0 <- withExpr sex2
               return sex1
          -- If we are multiplying by one, we can safely not do the
          -- multiply
          , do guard $ op == OpMul
               Lit _ 1 <- withExpr sex1
               return $ sex2
          -- If we are dividing by one, we can safely not do the
          -- divide
          , do guard $ op == OpDiv
               Lit _ 1 <- withExpr sex2
               return $ sex1
          -- If we are multiplying by zero a division, we may move the
          -- multiplication into the numerator.
          , do guard $ op == OpMul
               Lit _ 0 <- withExpr sex1
               BinOp binpos OpDiv num denom <- withExpr sex2
               simpES $ BinOp binpos OpDiv
                          (BinOp pos OpMul sex1 num)
                          denom
          -- We may distribute multiplication by zero over addition or
          -- subtraction
          , do guard $ op == OpMul
               Lit _ 0 <- withExpr sex1
               BinOp binpos op' a b <- withExpr sex2
               guard $ op' `elem` [OpAdd, OpSub]
               simpES $ BinOp binpos op'
                          (BinOp pos OpMul sex1 a)
                          (BinOp pos OpMul sex1 b)
          -- If we are multiplying a literal by the negation of
          -- something, we can move the negation to the literal as
          -- long as the literal isn't the most negative number.
          , do Lit litpos i <- withExpr sex1
               guard $ i /= minBound
               UnOp _ OpNeg nsex2 <- withExpr sex2
               simpES $ BinOp pos OpMul (Lit litpos (negate i)) nsex2
          -- Don't put in a default case.
          ]

binOp :: BinOp -> Int64 -> Int64 -> Int64
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

unOp :: UnOp -> Int64 -> Int64
unOp OpNeg = negate 
unOp OpNot = boolToInt . not . intToBool