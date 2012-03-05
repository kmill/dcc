{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, 
  FlexibleInstances #-}

-- | In this file, @<==>@ is an operator which means "unify".  This
-- file just does a semantic check, but doesn't bother to build a
-- symbol table.  It uses a unifier to make (possibly) nicer error messages.

module SemanticCheck(doSemanticCheck,
                     SemError(..),
                     DUType(..),
                     duTermPos,
                     showDUTerm)
    where

import AST
import Scanner (Token(..), TokenType(..))
import Text.ParserCombinators.Parsec (SourcePos)
import Unify
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Exceptional
import Control.Monad.Reader.Class
import Data.Maybe
import Text.Printf
import Data.List

-- | This is the main entry point.
doSemanticCheck :: DProgram
                -> Either (UnifierData DUType, [SemError]) LexicalEnv
doSemanticCheck ast = res
    where res = runSemChecker (checkDProgram ast)

---
--- Lexical environments
---

data LexicalEnv = LexicalEnv
    { lexicalBindings :: Map.Map String DUTerm
    , parentEnv :: Maybe LexicalEnv
    , methReturnType :: Maybe DUTerm -- the return type of the current function
    , isInsideLoop :: Bool
    }
                  deriving Show

emptyEnv :: LexicalEnv
emptyEnv = LexicalEnv { lexicalBindings=Map.empty
                      , parentEnv=Nothing 
                      , methReturnType=Nothing
                      , isInsideLoop=False }

-- | Recursively look up a binding.
envLookup :: String -> LexicalEnv -> Maybe DUTerm
envLookup name lenv = Map.lookup name e
                      `mplus` ((parentEnv lenv) >>= envLookup name)
    where e = lexicalBindings lenv

-- | Get the root environment of a lexical environment.
envRoot :: LexicalEnv -> LexicalEnv
envRoot env = maybe env envRoot (parentEnv env)

-- | Add binding to an environment
envBind :: String -> DUTerm -> LexicalEnv -> LexicalEnv
envBind name val lenv = lenv { lexicalBindings=Map.insert name val e }
    where e = lexicalBindings lenv

-- | Create a sub-environment of a lexical environment.
deriveEnv :: LexicalEnv -> LexicalEnv
deriveEnv e = LexicalEnv { lexicalBindings=Map.empty
                         , parentEnv=Just e
                         , methReturnType=methReturnType e
                         , isInsideLoop=isInsideLoop e}

-- | Creates a sub-environment while extending it with multiple bindings.
extendEnv :: [(String, DUTerm)] -> Maybe DUTerm -> LexicalEnv -> LexicalEnv
extendEnv bindings ret e
    = LexicalEnv
      { lexicalBindings=Map.fromList bindings
      , parentEnv=Just e
      , methReturnType=ret
      , isInsideLoop=isInsideLoop e }

-- | This is the type which represents Decaf types, which are unified
-- by the 'Unify' module.
type DUTerm = Term DUType

-- | This is the type of the head of the 'Term' type.
data DUType = DUInt SourcePos
            | DUBool SourcePos
            | DUChar SourcePos
            | DUString SourcePos
            | DUVoid SourcePos
            | DUArray SourcePos (Maybe Int)
            | DUFunc SourcePos
              deriving (Show)

-- | We have to make our own 'Eq' instance since 'SourcePos' shouldn't
-- matter for equality.
instance Eq DUType where
  (DUInt _) == (DUInt _) = True
  (DUBool _) == (DUBool _) = True
  (DUChar _) == (DUChar _) = True
  (DUString _) == (DUString _) = True
  (DUVoid _) == (DUVoid _) = True
  (DUArray _ _) == (DUArray _ _) = True
  (DUFunc _) == (DUFunc _) = True
  _ == _ = False

-- | Helpers for making instances of 'DUTerm'.
tInt, tBool, tChar, tString, tVoid :: SourcePos -> DUTerm
tInt pos = nullaryTerm (DUInt pos)
tBool pos = nullaryTerm (DUBool pos)
tChar pos = nullaryTerm (DUChar pos)
tString pos = nullaryTerm (DUString pos)
tVoid pos = nullaryTerm (DUVoid pos)

tArray :: SourcePos -> Maybe Int -> DUTerm -> DUTerm
tArray pos s t = Term (DUArray pos s) [t]

tFunc :: SourcePos -> DUTerm -> [DUTerm] -> DUTerm
tFunc pos r args = Term (DUFunc pos) ([r] ++ args)

-- | Our version of the unifier type!
type Unifier = ExceptionalT (UnificationError DUType) (State (UnifierData DUType))

instance MonadState (UnifierData DUType) Unifier where
    get = lift get
    put s = lift (put s)

instance BindingMonad DUType Unifier

data SemCheckData = SemCheckData
    { semUnifierData :: UnifierData DUType
    , semErrors :: [SemError]
    , semLexicalEnv :: LexicalEnv
    } deriving Show
    
data SemError = SemUnificationError (UnificationError DUType)
              | SemDupDef SourcePos String
              | SemUnboundError SourcePos String DUTerm
              | SemBreakOutsideLoop SourcePos
              | SemContinueOutsideLoop SourcePos
              | SemNoMainError SourcePos
              | SemNotScalarError DUTerm SourcePos
              | SemArraySizeError SourcePos
                deriving Show
                         
showDUTerm :: DUTerm -> String
showDUTerm (Var u) = show u
showDUTerm (Term (DUArray _ _) [x]) = printf "%s[]" (showDUTerm x)
showDUTerm (Term (DUFunc _) (ret:args)) = printf "%s (%s)"
                                        (showDUTerm ret)
                                        (intercalate ", "
                                         [showDUTerm a | a <- args])
showDUTerm (Term t _) = showDUType t

showDUType :: DUType -> String
showDUType (DUInt _) = "int"
showDUType (DUBool _) = "boolean"
showDUType (DUChar _) = "char"
showDUType (DUString _) = "string"
showDUType (DUVoid _) = "void"
showDUType _ = fail "Haven't figured this out yet"

duTypePos :: DUType -> SourcePos
duTypePos (DUInt pos) = pos
duTypePos (DUBool pos) = pos
duTypePos (DUChar pos) = pos
duTypePos (DUString pos) = pos
duTypePos (DUVoid pos) = pos
duTypePos (DUFunc pos) = pos
duTypePos (DUArray pos _) = pos

duTermPos :: DUTerm -> SourcePos
duTermPos (Term x _) = duTypePos x
duTermPos (Var _) = error "Attempted to retrieve source pos from unification variable"

duWithPos :: DUTerm -> SourcePos -> DUTerm
duWithPos v@(Var _) pos = v
duWithPos (Term t x) pos = Term updatedPos x
    where updatedPos = case t of
                         DUInt _ -> DUInt pos
                         DUBool _ -> DUBool pos
                         DUChar _ -> DUChar pos
                         DUString _ -> DUString pos
                         DUVoid _ -> DUVoid pos
                         DUFunc _ -> DUFunc pos
                         DUArray _ i -> DUArray pos i

-- | Our semantic checker monad!  We make our own state monad because
-- we want 'MonadState' and 'MonadReader' to not come by default.
newtype SemChecker a = SemChecker { getSemChecker :: State SemCheckData a }

instance Functor SemChecker where
    fmap f m = SemChecker (fmap f (getSemChecker m))

instance Monad SemChecker where
    return = SemChecker . return
    a >>= f =  SemChecker (getSemChecker a >>= (getSemChecker . f))
    
instance Applicative SemChecker where
    mf <*> mb = do f <- mf
                   b <- mb
                   return (f b)

-- | This instance of 'MonadReader' just defers to the embedded state monad.
instance MonadState SemCheckData SemChecker where
    get = SemChecker get
    put a = SemChecker $ put a

-- | This instance of 'MonadReader' gets the lexical environment out
-- of the semantic checker monad.
instance MonadReader LexicalEnv SemChecker where
  ask = do s <- get
           return $ semLexicalEnv s
  local f m = do s <- get
                 put $ s { semLexicalEnv = f $ semLexicalEnv s }
                 res <- m
                 s' <- get
                 put $ s' { semLexicalEnv = semLexicalEnv s }
                 return res

-- | This modifies the lexical environment in the state monad with
-- some arbitrary transformer function.
modEnv :: (LexicalEnv -> LexicalEnv) -> SemChecker ()
modEnv f = do s <- get
              put $ s { semLexicalEnv=f (semLexicalEnv s) }

-- | Adds an error to the current list of semantic errors.
addError :: SemError -> SemChecker ()
addError e = do sd <- get
                put $ sd { semErrors=semErrors sd ++ [e] }

-- | Used by the for-loop and while-loop handlers to signal when break
-- and continue are value.
enterLoop :: SemChecker a -> SemChecker a
enterLoop = local (\env -> env { isInsideLoop=True })

-- | Adds a binding to the current lexical environment, checking for
-- duplicate definitions and adding semantic errors in such an event.
addEnvBinding :: SourcePos -> String -> DUTerm -> SemChecker ()
addEnvBinding pos name typ
    = do env <- ask
         case Map.lookup name (lexicalBindings env) of
           Just _ -> addError $ SemDupDef pos name
           Nothing -> modEnv $ envBind name typ

-- | Attempts to look up the type of an identifier in the current
-- lexical environment, and if it fails, it adds an error and returns
-- a fresh unification variable as the type.  The unification variable
-- is attached to the semantic error so that the error message will be
-- able to include the inferred type of the unbound identifier.
lookupOrAdd :: SourcePos -> String -> SemChecker DUTerm
lookupOrAdd pos name
    = do env <- ask
         case envLookup name env of
           Just t -> return t
           Nothing -> do v <- fromJust <$> (liftS genVar)
                         addEnvBinding pos name (Var v)
                         addError $ SemUnboundError pos name (Var v)
                         return $ Var v

-- | This runs the semantic checker and provides either the error data
-- if there was a semantic error, or something irrelevant if there was
-- no error.
runSemChecker :: SemChecker a
              -> Either (UnifierData DUType, [SemError]) LexicalEnv
runSemChecker sc = let (_, s') = runState (getSemChecker sc) s
                   in case semErrors s' of
                        [] -> Right $ semLexicalEnv s'
                        errors -> Left (semUnifierData s', errors)
    where s = SemCheckData
              { semUnifierData=newUnifierData
              , semErrors=[]
              , semLexicalEnv=emptyEnv
              }

-- | This lifts a unification operation up into the semantic checker.
-- It pulls the unification data out of the state of the semantic
-- checker monad, runs the unification monad, and then puts the
-- resulting state back into the semantic checker monad.
liftS :: Unifier a -> SemChecker (Maybe a)
liftS m = do sd <- get
             let s = semUnifierData sd
             let (t, s') = runState (catchT (return <$> m) Exception) s
             case t of
               Success t' -> do put $ sd { semUnifierData=s' }
                                return $ Just t'
               Exception r -> do put $ sd { semErrors=semErrors sd
                                            ++ [SemUnificationError r] }
                                 return Nothing


-- the unification operator
infix 5 <==>

-- | Unifies two types, storing the error messages in the SemChecker
-- monad, and continues onward despite errors.  Read @<==>@ as "make
-- equality by modifying the structures on both sides".
(<==>) :: DUTerm -> DUTerm -> SemChecker ()
t1 <==> t2  = do liftS $ unify t1 t2
                 return ()

---
--- The actual semantic checks
---

checkDProgram :: DProgram -> SemChecker ()
checkDProgram (DProgram pos fdecls mdecls)
    = do sequence_ [checkFieldDecl f | f <- fdecls]
         sequence_ [checkMethodDecl m | m <- mdecls]
         env <- ask
         case envLookup "main" env of
           Just t -> do v <- fromJust <$> liftS genVar
                        -- duTermPos is OK since global-def will not be var
                        t <==> tFunc (duTermPos t) (Var v) [] -- check main has no args
                        return ()
           Nothing -> addError $ SemNoMainError pos

getDUType :: DType -> SourcePos -> DUTerm
getDUType DInt = tInt
getDUType DBool = tBool
         
checkFieldDecl :: FieldDecl -> SemChecker ()
checkFieldDecl (FieldDecl pos t vars)
     = sequence_ [checkvar v | v <- vars]
     where
       checkvar (PlainVar tok)
           = addEnvBinding (tokenPos tok) (tokenString tok)
             (getDUType t (tokenPos tok))
       checkvar (ArrayVar tok1 len)
           = do when (len <= 0) $ addError $ SemArraySizeError (tokenPos tok1)
                addEnvBinding (tokenPos tok1) (tokenString tok1)
                                  (tArray (tokenPos tok1) Nothing
                                              (getDUType t (tokenPos tok1)))

getMethodType :: MethodType -> SourcePos -> DUTerm             
getMethodType (MethodReturns t) = getDUType t
getMethodType MethodVoid = tVoid

getMArg :: MethodArg -> (String, DUTerm)
getMArg (MethodArg t tok) = (tokenString tok, getDUType t (tokenPos tok))

checkMethodDecl :: MethodDecl -> SemChecker ()
checkMethodDecl (MethodDecl pos t tok args st)
    = do addEnvBinding pos name ftyp
         local (extendEnv targs (Just retType)) (checkStatement st)
      where name = tokenString tok
            ftyp = tFunc (tokenPos tok) retType [atyp | (_,atyp) <- targs]
            retType = getMethodType t pos
            targs = map getMArg args

checkStatement :: Statement -> SemChecker ()
checkStatement (Block pos vdecls statements)
    = local deriveEnv $
      do sequence_ [checkVarDecl v | v <- vdecls]
         sequence_ [checkStatement s | s <- statements]
checkStatement (IfSt pos expr cst mast)
    = do et <- checkExpr expr
         tBool (getNodePos expr) <==> et
         checkStatement cst
         maybe (return ()) checkStatement mast
checkStatement (ForSt pos tok start end st)
    = do t1 <- checkExpr start
         tInt (getNodePos start) <==> t1
         t2 <- checkExpr end
         tInt (getNodePos end) <==> t2
         local deriveEnv $ do -- create environment to shadow variable if needed.
           addEnvBinding (tokenPos tok) (tokenString tok) (tInt $ tokenPos tok) -- add index variable
           enterLoop $ checkStatement st
checkStatement (WhileSt pos expr st)
    = do t <- checkExpr expr
         tBool (getNodePos expr) <==> t
         local deriveEnv $ do -- create environment to shadow variable if needed.
           enterLoop $ checkStatement st
checkStatement (ReturnSt pos mexpr)
    = do env <- ask
         let rettype = fromJust $ methReturnType env
         case mexpr of
           Nothing -> rettype <==> tVoid pos
           Just expr -> do t <- checkExpr expr
                           t <==> rettype
checkStatement (BreakSt pos)
    = do env <- ask
         case isInsideLoop env of
           True -> return ()
           False -> addError $ SemBreakOutsideLoop pos
checkStatement (ContinueSt pos)
    = do env <- ask
         case isInsideLoop env of
           True -> return ()
           False -> addError $ SemContinueOutsideLoop pos
checkStatement (ExprSt ex) = () <$ checkExpr ex
checkStatement (AssignSt pos loc assop ex)
    = do dt <- checkLocation loc
         et <- checkExpr ex
         case assop of
           Assign -> do checkIsScalar et (getNodePos ex)
                        (duWithPos dt (getNodePos loc))
                           <==> (duWithPos et (getNodePos ex))
           _ -> do et <==> tInt (getNodePos ex)
                   dt <==> tInt (getNodePos loc)

checkVarDecl :: VarDecl -> SemChecker ()
checkVarDecl (VarDecl pos t vars)
     = sequence_ [checkvar v | v <- vars]
     where
       checkvar tok
           = addEnvBinding pos' (tokenString tok) (getDUType t pos')
           where pos' = tokenPos tok

-- | Checks if a term is a scalar, if it is bound.  The assumption is
-- that if it is not bound, then we don't need to emit an error
-- because an error will be emitted for having made an unbound error.
checkIsScalar :: DUTerm -> SourcePos -> SemChecker ()
checkIsScalar t pos = case t of
                        (Var _) -> return ()
                        (Term x _) ->
                             case x of
                               (DUInt _) -> return ()
                               (DUBool _) -> return ()
                               _ -> addError $ SemNotScalarError t pos
             
checkExpr :: Expr -> SemChecker DUTerm
checkExpr (BinaryOp pos e1 tok e2)
    = if tokenString tok `elem` ["==", "!="]
      then do t1 <- checkExpr e1
              t2 <- checkExpr e2
              t1 <==> t2
              checkIsScalar t1 (getNodePos e1)
              return $ tBool pos
      else do t1 <- checkExpr e1
              t1 <==> neededType (tokenPos tok)
              t2 <- checkExpr e2
              t2 <==> neededType (tokenPos tok)
              return $ givesType pos
    where neededType
              = if tokenString tok `elem` boolArgBinOps
                then tBool else tInt
          boolArgBinOps = ["&&", "||"]
          givesType
              = if tokenString tok `elem` boolRetBinOps
                then tBool else tInt
          boolRetBinOps = ["&&", "||", "<", "<=", ">=", ">", "==", "!="]
checkExpr (UnaryOp pos tok expr)
    = do t <- checkExpr expr
         t <==> unType (tokenPos tok)
         return $ unType pos
    where unType = case tokenString tok of
                     "-" -> tInt
                     "!" -> tBool
                     _ -> fail "No such unary operator"
checkExpr (ExprLiteral pos tok)
    = case tokenType tok of
        CharLiteral -> return $ tChar pos
        StringLiteral -> return $ tString pos
        BooleanLiteral -> return $ tBool pos
        IntLiteral -> error "uh oh" -- This shouldn't be used because of ExprIntLiteral
        _ -> error "uh oh"
checkExpr (ExprIntLiteral pos tok)
    = return $ tInt pos
checkExpr (LoadLoc pos loc)
    = checkLocation loc
checkExpr (ExprMethod pos call)
    = checkMethodCall call
      
checkLocation :: DLocation -> SemChecker DUTerm
checkLocation (PlainLocation pos tok)
    = lookupOrAdd pos (tokenString tok)
checkLocation (ArrayLocation pos tok expr) -- tok[expr]
    = do t <- lookupOrAdd pos (tokenString tok)
         t' <- checkExpr expr
         t' <==> tInt (getNodePos expr)
         v <- fromJust <$> (liftS genVar)
         t <==> tArray pos Nothing (Var v)
         return $ Var v

checkMethodCall :: MethodCall -> SemChecker DUTerm
checkMethodCall (NormalMethod pos tok args)
    = do env <- ask
         v <- fromJust <$> (liftS genVar)
         targs' <- targs
         case envLookup name env of
           Just t -> do t <==> tFunc pos (Var v) targs'
                        return $ Var v
           Nothing -> local envRoot $
                      do ft <- lookupOrAdd pos name
                         ft <==> tFunc pos (Var v) targs'
                         return $ Var v
    where targs = sequence [checkExpr a | a <- args]
          name = tokenString tok
checkMethodCall (CalloutMethod pos tok args)
    = do sequence_ [checkCArg a | a <- args]
         return $ tInt pos
    where checkCArg (CArgString _) = return ()
          checkCArg (CArgExpr ex) = () <$ checkExpr ex