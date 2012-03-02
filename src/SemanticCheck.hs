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
import Execution
import Data.Int

-- | This is the main entry point.
doSemanticCheck :: DProgram
                -> Either (UnifierData DUType, [SemError]) LexicalEnv
doSemanticCheck ast = res
    where res = runSemChecker (runDProgram ast)

--- environments

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
    
envLookup :: String -> LexicalEnv -> Maybe DUTerm
envLookup name lenv = Map.lookup name e
                      `mplus` ((parentEnv lenv) >>= envLookup name)
    where e = lexicalBindings lenv

envRoot :: LexicalEnv -> LexicalEnv
envRoot env = maybe env envRoot (parentEnv env)

envBind :: String -> DUTerm -> LexicalEnv -> LexicalEnv
envBind name val lenv = lenv { lexicalBindings=Map.insert name val e }
    where e = lexicalBindings lenv
          
deriveEnv :: LexicalEnv -> LexicalEnv
deriveEnv e = LexicalEnv { lexicalBindings=Map.empty
                         , parentEnv=Just e
                         , methReturnType=methReturnType e
                         , isInsideLoop=isInsideLoop e}

extendEnv :: [(String, DUTerm)] -> Maybe DUTerm -> LexicalEnv -> LexicalEnv
extendEnv bindings ret e
    = LexicalEnv
      { lexicalBindings=Map.fromList bindings
      , parentEnv=Just e
      , methReturnType=ret
      , isInsideLoop=isInsideLoop e }
      
type DUTerm = Term DUType

-- | "Decaf Unification Type"
data DUType = DUInt SourcePos
            | DUBool SourcePos
            | DUChar SourcePos
            | DUString SourcePos
            | DUVoid SourcePos
            | DUArray SourcePos (Maybe Int64)
            | DUFunc SourcePos
              deriving (Show)

instance Eq DUType where
  (DUInt _) == (DUInt _) = True
  (DUBool _) == (DUBool _) = True
  (DUChar _) == (DUChar _) = True
  (DUString _) == (DUString _) = True
  (DUVoid _) == (DUVoid _) = True
  (DUArray _ _) == (DUArray _ _) = True
  (DUFunc _) == (DUFunc _) = True
  _ == _ = False

-- | Helpers for making instances of @DUTerm@.
tInt, tBool, tChar, tString, tVoid :: SourcePos -> DUTerm
tInt pos = nullaryTerm (DUInt pos)
tBool pos = nullaryTerm (DUBool pos)
tChar pos = nullaryTerm (DUChar pos)
tString pos = nullaryTerm (DUString pos)
tVoid pos = nullaryTerm (DUVoid pos)

tArray :: SourcePos -> Maybe Int64 -> DUTerm -> DUTerm
tArray pos s t = Term (DUArray pos s) [t]

tFunc :: SourcePos -> DUTerm -> [DUTerm] -> DUTerm
tFunc pos r args = Term (DUFunc pos) ([r] ++ args)

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
                    
newtype SemChecker a = SemChecker { getSemChecker :: State SemCheckData a }

instance Functor SemChecker where
    fmap f m = SemChecker (fmap f (getSemChecker m))

instance Monad SemChecker where
    return = SemChecker . return
    a >>= f =  SemChecker (getSemChecker a >>= (getSemChecker . f))

instance MonadState SemCheckData SemChecker where
    get = SemChecker get
    put a = SemChecker $ put a

instance MonadReader LexicalEnv SemChecker where
  ask = do s <- get
           return $ semLexicalEnv s
  local f m = do s <- get
                 put $ s { semLexicalEnv = f $ semLexicalEnv s }
                 res <- m
                 s' <- get
                 put $ s' { semLexicalEnv = semLexicalEnv s }
                 return res

modEnv :: (LexicalEnv -> LexicalEnv) -> SemChecker ()
modEnv f = do s <- get
              put $ s { semLexicalEnv=f (semLexicalEnv s) }
              
addError :: SemError -> SemChecker ()
addError e = do sd <- get
                put $ sd { semErrors=semErrors sd ++ [e] }

enterLoop :: SemChecker a -> SemChecker a
enterLoop = local (\env -> env { isInsideLoop=True })
              
              
addEnvBinding :: SourcePos -> String -> DUTerm -> SemChecker ()
addEnvBinding pos name typ
    = do env <- ask
         case Map.lookup name (lexicalBindings env) of
           Just _ -> addError $ SemDupDef pos name
           Nothing -> modEnv $ envBind name typ

lookupOrAdd :: SourcePos -> String -> SemChecker DUTerm
lookupOrAdd pos name
    = do env <- ask
         case envLookup name env of
           Just t -> return t
           Nothing -> do v <- fromJust <$> (liftS genVar)
                         addEnvBinding pos name (Var v)
                         addError $ SemUnboundError pos name (Var v)
                         return $ Var v

runSemChecker :: SemChecker a
              -> Either (UnifierData DUType, [SemError]) LexicalEnv
runSemChecker sc = let (t, s') = runState (getSemChecker sc) s
                   in case semErrors s' of
                        [] -> Right $ semLexicalEnv s'
                        errors -> Left (semUnifierData s', errors)
    where s = SemCheckData
              { semUnifierData=newUnifierData
              , semErrors=[]
              , semLexicalEnv=emptyEnv
              }

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

(<==>) :: DUTerm -> DUTerm -> SemChecker (Maybe DUTerm)
t1 <==> t2  = liftS $ unify t1 t2

getDUType DInt = tInt
getDUType DBool = tBool

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

instance ASTExecution SemChecker DUTerm DUTerm where
  doDProgram pos fdecls mdecls
      = do sequence_ fdecls
           sequence_ mdecls
           env <- ask
           case envLookup "main" env of
             Just t -> do v <- fromJust <$> liftS genVar
                          -- duTermPos is OK since global-def will not be uvar.
                          -- check that main has no args
                          _ <- t <==> tFunc (duTermPos t) (Var v) []
                          return ()
             Nothing -> addError $ SemNoMainError pos
  
  doFieldScalar pos typ name
      = addEnvBinding pos name (getDUType typ pos)
  doFieldArray pos typ name len
      = do when (len <= 0) $ addError $ SemArraySizeError pos
           addEnvBinding pos name
                             (tArray pos (Just len) (getDUType typ pos))
  
  getMethodArg pos typ name
    = return $ getDUType typ pos
    
  doMethodDecl pos typ fpos name args st
      = do args' <- sequence args
           let ftyp = tFunc fpos retType [t' | (_,t') <- args']
           addEnvBinding pos name ftyp
           local (extendEnv args' (Just retType)) st
      where retType = getMethodType typ pos
            getMethodType mtype
              = case mtype of
                  MethodReturns t -> getDUType t
                  MethodVoid -> tVoid
  
  doVarDecl pos t n
      = addEnvBinding pos n (getDUType t pos)
                  
  doBlock pos vdecls sts
      = local deriveEnv $ do
          sequence_ vdecls
          sequence_ sts
  doIfSt pos expr cons malt
      = do e <- expr
           _ <- tBool pos <==> e
           cons
           fromMaybe (return ()) malt
  doForSt ipos iname spos start epos end st
      = do t1 <- start
           _ <- tInt spos <==> t1
           t2 <- end
           _ <- tInt epos <==> t2
           local deriveEnv $ do
             addEnvBinding ipos iname (tInt ipos)
             enterLoop st
  doWhileSt pos expr st
      = do t <- expr
           _ <- tBool pos <==> t
           enterLoop st
  doVoidReturn pos
      = do env <- ask
           let rettype = fromJust $ methReturnType env
           _ <- rettype <==> tVoid pos
           return ()
  doReturn expr
      = do t <- expr
           env <- ask
           let rettype = fromJust $ methReturnType env
           _ <- rettype <==> t
           return ()
  doBreakSt pos
      = do env <- ask
           unless (isInsideLoop env) $ do
             addError $ SemBreakOutsideLoop pos
  doContinueSt pos
      = do env <- ask
           unless (isInsideLoop env) $ do
             addError $ SemContinueOutsideLoop pos
             
  doAssignSt lpos loc assop expos ex
      = do dt <- fst loc
           et <- ex
           checkIsScalar et expos
           dt <- (maybe et id) <$> dt <==> et
           case assop of
             Assign    -> return ()
             IncAssign -> dt <==> tInt lpos  >> return ()
             DecAssign -> dt <==> tInt lpos   >> return ()

  doBinOp oppos op e1pos e1 e2pos e2
      = if op `elem` ["==", "!="]
        then do t1 <- e1
                t2 <- e2
                _ <- t1 <==> t2
                checkIsScalar t1 e1pos
                return $ tBool oppos
        else do t1 <- e1
                _ <- t1 <==> neededType oppos
                t2 <- e2
                _ <- t2 <==> neededType oppos
                return $ givesType oppos
      where neededType
                = if op `elem` boolArgBinOps
                  then tBool else tInt
            boolArgBinOps = ["&&", "||"]
            givesType
                = if op `elem` boolRetBinOps
                  then tBool else tInt
            boolRetBinOps = ["&&", "||", "<", "<=", ">=", ">", "==", "!="]
  doUnaryOp oppos op expos ex
      = do t <- ex
           _ <- t <==> unType oppos
           return $ unType oppos
      where unType = case op of
                       "-" -> tInt
                       "!" -> tBool
                       _ -> error "No such unary operator"
                       
  doLiteral pos typ str
      = case typ of
          CharLiteral -> return $ tChar pos
          StringLiteral -> return $ tString pos
          BooleanLiteral -> return $ tBool pos
          IntLiteral -> error "uh oh" -- shouldn't be used
          _ -> error "uh oh"
  doIntLiteral pos i
      = return $ tInt pos
        
  doScalarLocation pos n = (lookupOrAdd pos n, const $ return ())
  doArrayLocation pos n epos e
      = (arrType, const $ return ())
      where arrType
                = do t <- lookupOrAdd pos n
                     t' <- e
                     _ <- t' <==> tInt epos
                     v <- fromJust <$> (liftS genVar)
                     mt <- t <==> tArray pos Nothing (Var v)
                     return $ Var v
           
  doNormalMethod pos name args
      = do env <- ask
           v <- fromJust <$> (liftS genVar)
           targs <- sequence args
           case envLookup name env of
             Just t -> do _ <- t <==> tFunc pos (Var v) targs
                          return $ Var v
             Nothing -> local envRoot $
                        do ft <- lookupOrAdd pos name
                           _ <- ft <==> tFunc pos (Var v) targs
                           return $ Var v
  doCalloutMethod pos name cargs
      = do sequence_ (map checkarg cargs)
           return $ tInt pos
      where checkarg (Left _) = return $ tInt pos -- no-op
            checkarg (Right ex) = ex
