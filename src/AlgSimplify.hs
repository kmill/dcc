{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}

-- | It is imperative to justify all rules put into the simplifier.
-- For instance, you can't negate the most negative integer safely!

module AlgSimplify(algSimplifyInst, flattenOp) where

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
            DivStore pos v op (Lit pos' num) (Lit _ denom) ->
                do guard $ denom /= 0
                   return $ Store pos v (Lit pos' (f num denom))
                where f = case op of
                            DivQuo -> quot
                            DivRem -> rem
            DivStore pos v DivQuo num (Lit _ 1) ->
                return $ Store pos v num
            DivStore pos v DivQuo num (Lit pos' (-1)) ->
                do num' <- simpES $ UnOp pos' OpNeg num
                   return $ Store pos v num'
            DivStore pos v op exp1 exp2 ->
                do [exp1', exp2'] <- simpEMany [exp1, exp2]
                   let inst' = DivStore pos v op exp1' exp2'
                   simpI inst' `mplus` return inst'
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
              msum [ do exp' <- simpE exp
                        case exp' of
                          Lit _ x -> return $ Branch pos
                                     $ if intToBool x then tl else fl
                          _ -> return $ CondBranch pos exp' tl fl
                   , do exp' <- simpES exp
                        case exp' of
                          Lit _ x ->
                            return $ Branch pos
                            $ if intToBool x then tl else fl
                          _ -> mzero
                   ]
            Return pos from (Just exp) ->
                do exp' <- simpE exp
                   return $ Return pos from (Just exp')
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

simpUnOp :: (Show v, Ord v) => SourcePos -> UnOp -> Expr v -> AM (Expr v)
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
          -- Negating a subtraction is the same as reversing the
          -- subtraction
          , do guard $ op == OpNeg
               BinOp pos2 OpSub sex1 sex2 <- withExpr sex
               simpES $ BinOp pos2 OpSub sex2 sex1
          -- Negating an addition with a constant is the same as
          -- subtracting from the negative constant
          , do guard $ op == OpNeg
               BinOp pos2 OpAdd (Lit litpos i) sex2 <- withExpr sex
               guard $ i /= minBound
               simpES $ BinOp pos2 OpSub (Lit litpos (negate i)) sex2
          -- Negating a subtraction with a constant is the same as
          -- adding to the negative constant
          , do guard $ op == OpNeg
               BinOp pos2 OpSub (Lit litpos i) sex2 <- withExpr sex
               guard $ i /= minBound
               simpES $ BinOp pos2 OpAdd (Lit litpos (negate i)) sex2
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
            -- constants. (there is no division operation).
            -- Muchnick R1,R3,R5
            do Lit _ i1 <- withExpr sex1
               Lit _ i2 <- withExpr sex2
               return $ Lit pos (binOp op i1 i2)
          -- The following rule enforces the order that literals occur
          -- at the beginning of a sequence of
          -- additions or multiplications
          -- Muchnick R2,R4
          , do guard $ op `elem` [OpAdd, OpMul]
               guard $ sex1 > sex2
               simpES $ BinOp pos op sex2 sex1
          -- Reassociates left-association to right-association for
          -- addition and multiplication while reordering the three
          -- expressions.
          -- backwards Muchnick R7,R8
          , do guard $ op `elem` [OpAdd, OpMul]
               BinOp _ op' oper1 oper2 <- withExpr sex1
               guard $ op' == op
               guard $ oper2 > sex2
               let [a, b, c] = sort [oper1, oper2, sex2]
               oper1' <- simpES $ BinOp pos op a b
               simpES $ BinOp pos op oper1' c
          -- Pulls a constant from the right branch into the left
          -- branch if the left is a constant, too
          -- Backwards muchnick R9, R10
          , do guard $ op `elem` [OpAdd, OpMul]
               Lit litpos i1 <- withExpr sex1
               BinOp _ op' (Lit _ i2) sex2_2 <- withExpr sex2
               guard $ op == op'
               simpES $ BinOp pos op (Lit litpos (binOp op i1 i2)) sex2_2
          -- Reorders the tree if the right-side's left branch is less
          -- than the left branch
          , do guard $ op `elem` [OpAdd, OpMul]
               BinOp pos2 op' sex2_1 sex2_2 <- withExpr sex2
               guard $ op == op'
               guard $ sex1 > sex2_1
               simpES $ BinOp pos op sex2_1 (BinOp pos2 op sex1 sex2_2)
          -- Adding a negation is the same as just subtracting
          , do guard $ op == OpAdd
               UnOp pos1 OpNeg nsex1 <- withExpr sex1
               simpES $ BinOp pos1 OpSub sex2 nsex1
          , do guard $ op == OpAdd
               UnOp pos1 OpNeg nsex2 <- withExpr sex2
               simpES $ BinOp pos1 OpSub sex1 nsex2
          -- pulls a constant from the right subtraction branch for an
          -- addition.
          , do guard $ op == OpAdd
               BinOp pos2 OpSub (Lit litpos i) sex2_2 <- withExpr sex2
               simpES $ BinOp pos OpSub
                          (BinOp pos2 OpAdd
                           (Lit litpos i) sex1)
                          sex2_2
          -- Subtracting from a negation is the same as negating the
          -- addition
          , do guard $ op == OpSub
               UnOp pos1 OpNeg nsex1 <- withExpr sex1
               simpES $ UnOp pos1 OpNeg $ BinOp pos OpAdd nsex1 sex2
          -- Subtracting a negation is the same as addition
          , do guard $ op == OpSub
               UnOp _ OpNeg nsex2 <- withExpr sex2
               simpES $ BinOp pos OpAdd sex1 nsex2
          -- Pulls a constant from the right of a subtraction if it
          -- isn't the most negative number.
          , do guard $ op == OpSub
               BinOp pos2 OpAdd (Lit posi i2) sex2_2 <- withExpr sex2
               guard $ i2 /= minBound
               simpES $ BinOp pos OpSub
                          (BinOp pos2 OpAdd (Lit posi (negate i2)) sex1)
                          sex2_2
          -- Pulls a constant from the left of a subtraction into
          -- being an addition.
          , do guard $ op == OpSub
               BinOp pos1 OpAdd (Lit posi i) sex1_2 <- withExpr sex1
               simpES $ BinOp pos OpAdd
                          (Lit posi i)
                          (BinOp pos OpSub sex1_2 sex2)
          -- If subtracting a number, we can just add the negative of
          -- the number if it isn't the most negative number
          , do guard $ op == OpSub
               Lit pos2 i2 <- withExpr sex2
               guard $ i2 /= minBound
               simpES $ BinOp pos OpAdd sex1 (Lit pos2 (negate i2))
          -- If we are adding zero, we can safely not add the zero
          , do guard $ op == OpAdd
               Lit _ 0 <- withExpr sex1
               return $ sex2
          -- If we are subtracting from zero, we can do a negation.
          -- Muchnick R6
          , do guard $ op == OpSub
               Lit _ 0 <- withExpr sex1
               simpES $ UnOp pos OpNeg sex2
          -- If we are subtracting a zero, we can just not do that.
          , do guard $ op == OpSub
               Lit _ 0 <- withExpr sex2
               return sex1
          -- If we are subtracting something from itself, we can just do 0.
          , do guard $ op == OpSub
               guard $ sex1 == sex2
               return $ Lit pos 0
          -- If we are multiplying by one, we can safely not do the
          -- multiply
          , do guard $ op == OpMul
               Lit _ 1 <- withExpr sex1
               return $ sex2
          -- If we are dividing by one, we can safely not do the
          -- divide
--          , do guard $ op == OpDiv
--               Lit _ 1 <- withExpr sex2
--               return $ sex1
          -- If we are multiplying by zero a division, we may move the
          -- multiplication into the numerator.
--          , do guard $ op == OpMul
--               Lit _ 0 <- withExpr sex1
--               BinOp binpos OpDiv num denom <- withExpr sex2
--               simpES $ BinOp binpos OpDiv
--                          (BinOp pos OpMul sex1 num)
--                          denom

          -- Multiplication by zero is definitely zero (no need to
          -- worry about removing a division because that's in
          -- DivStore)
          , do guard $ op == OpMul
               Lit _ 0 <- withExpr sex1
               return sex1
          -- Muchick R11
          , do guard $ op == OpMul
               Lit posl1 i1 <- withExpr sex1
               BinOp pos2 OpAdd (Lit posl2 i2) sex2_2 <- withExpr sex2
               simpES $ BinOp pos OpAdd
                          (Lit posl1 (binOp op i1 i2))
                          (BinOp pos2 OpMul (Lit posl1 i1) sex2_2)
          -- If we are multiplying a literal by the negation of
          -- something, we can move the negation to the literal as
          -- long as the literal isn't the most negative number.
          , do Lit litpos i <- withExpr sex1
               guard $ i /= minBound
               UnOp _ OpNeg nsex2 <- withExpr sex2
               simpES $ BinOp pos OpMul (Lit litpos (negate i)) nsex2
          , do guard $ op `elem` cmpOps
               guard $ sex1 > sex2
               simpES $ BinOp pos (flipCmpOp op) sex2 sex1
          , do guard $ op `elem` cmpOps
               Lit _ 0 <- withExpr sex1
               BinOp pos2 OpSub sex2_1 sex2_2 <- withExpr sex2
               simpES $ BinOp pos op sex2_2 sex2_1
          , do guard $ op `elem` cmpOps
               Lit _ 0 <- withExpr sex1
               BinOp pos2 OpAdd (Lit litpos i) sex2_2  <- withExpr sex2
               guard $ i /= minBound
               simpES $ BinOp pos op (Lit litpos (negate i)) sex2_2
          -- Don't put in a default case.
          ]

binOp :: BinOp -> Int64 -> Int64 -> Int64
binOp OpAdd = (+)
binOp OpSub = (-)
binOp OpMul = (*)
--binOp OpDiv = quot
--binOp OpMod = rem
binOp CmpLT = \x y -> boolToInt $ x < y
binOp CmpGT = \x y -> boolToInt $ x > y 
binOp CmpLTE = \x y -> boolToInt $ x <= y 
binOp CmpGTE = \x y -> boolToInt $ x >= y 
binOp CmpEQ = \x y -> boolToInt $ x == y 
binOp CmpNEQ = \x y -> boolToInt $ x /= y

unOp :: UnOp -> Int64 -> Int64
unOp OpNeg = negate 
unOp OpNot = boolToInt . not . intToBool

cmpOps = [CmpLT, CmpGT, CmpLTE, CmpGTE, CmpEQ, CmpNEQ]
flipCmpOp CmpLT = CmpGT
flipCmpOp CmpGT = CmpLT
flipCmpOp CmpLTE = CmpGTE
flipCmpOp CmpGTE = CmpLTE
flipCmpOp CmpEQ = CmpEQ
flipCmpOp CmpNEQ = CmpNEQ
flipCmpOp _ = error "flipCmpOp: Not a comparison!"