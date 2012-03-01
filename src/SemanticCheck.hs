{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, 
  FlexibleInstances #-}

module SemanticCheck where

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
import Debug.Trace
import Text.Printf
import Data.List

doSemanticCheck :: DProgram
                -> Either (UnifierData DUType, [SemError]) LexicalEnv
doSemanticCheck ast = res
    where res = runSemChecker (checkDProgram ast)

--- environments

data LexicalEnv = LexicalEnv
    { lexicalBindings :: Map.Map String DUTerm
    , parentEnv :: Maybe LexicalEnv }
                  deriving Show
    
emptyEnv = LexicalEnv { lexicalBindings=Map.empty, parentEnv=Nothing }
    
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
deriveEnv e = LexicalEnv { lexicalBindings=Map.empty, parentEnv=Just e }

extendEnv :: [(String, DUTerm)] -> LexicalEnv -> LexicalEnv
extendEnv bindings e
    = LexicalEnv
      { lexicalBindings=Map.fromList bindings
      , parentEnv=Just e }

---

data DUType = DUInt SourcePos
            | DUBool SourcePos
            | DUChar SourcePos
            | DUString SourcePos
            | DUVoid SourcePos
            | DUArray (Maybe Int)
            | DUFunc SourcePos
              deriving (Show)

instance Eq DUType where
  (DUInt _) == (DUInt _) = True
  (DUBool _) == (DUBool _) = True
  (DUChar _) == (DUChar _) = True
  (DUString _) == (DUString _) = True
  (DUVoid _) == (DUVoid _) = True
  (DUArray _) == (DUArray _) = True
  (DUFunc _) == (DUFunc _) = True
  _ == _ = False

tInt pos = nullaryTerm (DUInt pos)
tBool pos = nullaryTerm (DUBool pos)
tChar pos = nullaryTerm (DUChar pos)
tString pos = nullaryTerm (DUString pos)
tVoid pos = nullaryTerm (DUVoid pos)
tArray s t = Term (DUArray s) [t]
tFunc pos r args = Term (DUFunc pos) ([r] ++ args)

type DUTerm = Term DUType

type Unifier = ExceptionalT (UnificationError DUType) (State (UnifierData DUType))

instance MonadState (UnifierData DUType) Unifier where
    get = lift get
    put s = lift (put s)

instance BindingMonad DUType Unifier

--testunify :: Unifier (Term DUType)
--testunify = let t1 = Term DUInt []
--                t2 = Var (UVar 0)
--                t3 = Term DUBool []
--            in unify t1 t2
               
data SemCheckData = SemCheckData
    { semUnifierData :: UnifierData DUType
    , semErrors :: [SemError]
    , semLexicalEnv :: LexicalEnv
    } deriving Show
    
data SemError = SemUnificationError (UnificationError DUType)
              | SemDupDef SourcePos String
              | SemUnboundError SourcePos String (Term DUType)
                deriving Show
                         
showDUTerm :: DUTerm -> String
showDUTerm (Var u) = show u
showDUTerm (Term (DUArray _) [x]) = printf "%s[]" (showDUTerm x)
showDUTerm (Term (DUFunc _) (ret:args)) = printf "%s (%s)"
                                        (showDUTerm ret)
                                        (intercalate ", "
                                         [showDUTerm a | a <- args])
showDUTerm (Term t _) = showDUType t

showDUType (DUInt _) = "int"
showDUType (DUBool _) = "boolean"
showDUType (DUChar _) = "char"
showDUType (DUString _) = "string"
showDUType (DUVoid _) = "void"

duTypePos (DUInt pos) = pos
duTypePos (DUBool pos) = pos
duTypePos (DUChar pos) = pos
duTypePos (DUString pos) = pos
duTypePos (DUVoid pos) = pos
duTypePos (DUFunc pos) = pos
--duTypePos _ = ""

--duTermPos (Var _) = ""
duTermPos (Term x _) = duTypePos x
                    
type SemChecker = State SemCheckData

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
              
              
addEnvBinding :: SourcePos -> String -> DUTerm -> SemChecker ()
addEnvBinding pos name typ
    = do env <- ask
         case envLookup name env of
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
runSemChecker sc = let (t, s') = runState sc s
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

doUnify :: Term DUType -> Term DUType -> SemChecker (Maybe (Term DUType))
doUnify t1 t2 = do sd <- get
                   let s = semUnifierData sd
                   let u = unify t1 t2 -- :: Unifier (Term DUType)
                   let (t, s') = runState (catchT (return <$> u) Exception) s
                   case t of
                     Success t' -> do put $ sd { semUnifierData=s' }
                                      return $ Just t'
                     Exception r -> do put $ sd { semErrors=semErrors sd
                                                  ++ [SemUnificationError r] }
                                       return Nothing
                                       
t1 <==> t2  = doUnify t1 t2

--runUnifier :: Unifier a -> Exceptional (UnificationError DUType) a
--runUnifier u = evalState s (catchT (return <$> u) Exception)
--    where s = 
               
--testunify2 = do let t1 = Term DUInt []
--                t2 <- Var <$> genVar "y"
--                t2 <- Var <$> genVar "y"
--                unify t1 t2
             
checkDProgram :: DProgram -> SemChecker ()
checkDProgram (DProgram _ fdecls mdecls)
    = do sequence_ [checkFieldDecl f | f <- fdecls]
         sequence_ [checkMethodDecl m | m <- mdecls]

getDUType DInt = tInt
getDUType DBool = tInt
         
checkFieldDecl :: FieldDecl -> SemChecker ()
checkFieldDecl (FieldDecl pos t vars)
     = sequence_ [checkvar v | v <- vars]
     where
       checkvar (PlainVar tok)
           = addEnvBinding pos (tokenString tok) (getDUType t pos)
       checkvar (ArrayVar tok1 tok2)
           = addEnvBinding pos (tokenString tok1) (tArray Nothing (getDUType t pos))
             
getMethodType (MethodReturns t) = getDUType t
getMethodType MethodVoid = tVoid

getMArg (MethodArg t tok) = (tokenString tok, getDUType t (tokenPos tok))

checkMethodDecl :: MethodDecl -> SemChecker ()
checkMethodDecl (MethodDecl pos t tok args st)
    = do addEnvBinding pos name ftyp
         local (extendEnv targs) (checkStatement st)
      where name = tokenString tok
            ftyp = tFunc pos (getMethodType t pos) [atyp | (_,atyp) <- targs]
            targs = map getMArg args

checkStatement :: Statement -> SemChecker ()
checkStatement (Block pos vdecls statements)
    = local deriveEnv $
      do sequence_ [checkVarDecl v | v <- vdecls]
         sequence_ [checkStatement s | s <- statements]
checkStatement (IfSt pos expr cst mast)
    = do et <- checkExpr expr
         _ <- liftS $ unify (tBool (getNodePos expr)) et
         checkStatement cst
         maybe (return ()) checkStatement mast
checkStatement (ForSt pos tok start end st)
    = do inc <- lookupOrAdd (tokenPos tok) (tokenString tok)
         _ <- liftS $ unify (tInt (tokenPos tok)) inc
         t1 <- checkExpr start
         _ <- liftS $ unify (tInt (getNodePos start)) t1
         t2 <- checkExpr end
         _ <- liftS $ unify (tInt (getNodePos start)) t1
         checkStatement st
checkStatement (WhileSt pos expr st)
    = do t <- checkExpr expr
         _ <- liftS $ unify (tBool (getNodePos expr)) t
         checkStatement st
checkStatement (ReturnSt pos mexpr)
    = return () -- TODO
checkStatement (BreakSt pos)
    = return () -- TODO should check inside loop
checkStatement (ContinueSt pos)
    = return () -- TODO should check inside loop
checkStatement (ExprSt ex) = () <$ checkExpr ex
checkStatement (AssignSt pos loc assop ex)
    = do dt <- checkLocation loc
         et <- checkExpr ex
         dt <- (maybe et id) <$> (liftS $ unify dt et)
         case assop of
           Assign -> return ()
           IncAssign -> () <$ liftS (unify dt (tInt pos))
           DecAssign -> () <$ liftS (unify dt (tInt pos))

checkVarDecl :: VarDecl -> SemChecker ()
checkVarDecl (VarDecl pos t vars)
     = sequence_ [checkvar v | v <- vars]
     where
       checkvar tok
           = addEnvBinding pos (tokenString tok) (getDUType t pos)
             
checkExpr :: Expr -> SemChecker (Term DUType)
checkExpr (BinaryOp pos e1 tok e2)
    = do t1 <- checkExpr e1
         _ <- liftS $ unify t1 (neededType (tokenPos tok))
         t2 <- checkExpr e2
         _ <- liftS $ unify t2 (neededType (tokenPos tok))
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
         _ <- liftS $ unify t (unType (tokenPos tok))
         return $ unType pos
    where unType = case tokenString tok of
                     "-" -> tInt
                     "!" -> tBool
checkExpr (ExprLiteral pos tok)
    = case tokenType tok of
        CharLiteral -> return $ tChar pos
        StringLiteral -> return $ tString pos
        BooleanLiteral -> return $ tBool pos
        IntLiteral -> return $ tInt pos
        _ -> error "uh oh"
checkExpr (LoadLoc pos loc)
    = checkLocation loc
checkExpr (ExprMethod pos call)
    = checkMethodCall call
      
checkLocation :: DLocation -> SemChecker (Term DUType)
checkLocation (PlainLocation pos tok)
    = lookupOrAdd pos (tokenString tok)
checkLocation (ArrayLocation pos tok expr) -- tok[expr]
    = do t <- lookupOrAdd pos (tokenString tok)
         t' <- checkExpr expr
         _ <- liftS $ unify (tInt (getNodePos expr)) t'
         v <- fromJust <$> (liftS genVar)
         mt <- liftS $ unify t (tArray Nothing (Var v))
         return $ Var v

checkMethodCall :: MethodCall -> SemChecker (Term DUType)
checkMethodCall (NormalMethod pos tok args)
    = do env <- ask
         v <- fromJust <$> (liftS genVar)
         targs' <- targs
         case envLookup name env of
           Just t -> do _ <- liftS $ unify t (tFunc pos (Var v) targs')
                        return $ Var v
           Nothing -> local envRoot $
                      do ft <- lookupOrAdd pos name
                         _ <- liftS $ unify ft (tFunc pos (Var v) targs')
                         return $ Var v
    where targs = sequence [checkExpr a | a <- args]
          name = tokenString tok
checkMethodCall (CalloutMethod pos tok args)
    = do sequence_ [checkCArg a | a <- args]
         (Var . fromJust) <$> (liftS genVar)
    where checkCArg (CArgString _) = return ()
          checkCArg (CArgExpr ex) = () <$ checkExpr ex