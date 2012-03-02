{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, 
  FlexibleInstances, FunctionalDependencies #-}

module Execution where

import AST
import Scanner(Token(..), TokenType(..))
import Text.ParserCombinators.Parsec (SourcePos)
import Control.Applicative
import Data.Int
import Data.Maybe

-- | This type holds what to do when loading or storing a location.
-- The first entry is "load" and the second entry is "store".
type Assigner m a = (m a, a -> m ())

class (Functor m, Monad m) => ASTExecution m arg expr | m -> arg expr where
    doDProgram :: SourcePos
               -> [m ()] -- ^ field decls
               -> [m ()] -- ^ method decls
               -> m ()
    doFieldScalar :: SourcePos
                  -> DType -- ^ scalar field type 
                  -> String -- ^ field identifier
                  -> m ()
    doFieldArray :: SourcePos
                 -> DType -- ^ underlying type of array
                 -> String -- ^ array identifier
                 -> Int64 -- ^ array length
                 -> m ()
    doMethodDecl :: SourcePos
                 -> MethodType -- ^ return type
                 -> SourcePos -- ^ position of identifier
                 -> String -- ^ method identifier
                 -> [m (String, arg)] -- ^ method arguments
                 -> m () -- ^ method body
                 -> m ()
    getMethodArg :: SourcePos
                 -> DType -- ^ argument type 
                 -> String -- ^ argument name
                 -> m arg
    doVarDecl :: SourcePos
              -> DType -- ^ var type
              -> String -- ^ var identifier
              -> m ()
    doBlock :: SourcePos
            -> [m ()] -- ^ varDecls
            -> [m ()] -- ^ statements
            -> m ()
    doIfSt :: SourcePos -- ^ pos of expr
           -> m expr -- ^ conditional
           -> m () -- ^ consequent
           -> Maybe (m ()) -- ^ alternate
           -> m ()
    doForSt :: SourcePos -- ^ pos of i
            -> String -- ^ name of i
            -> SourcePos -- ^ pos of start
            -> m expr -- ^ start
            -> SourcePos -- ^ pos of end
            -> m expr -- ^ end
            -> m () -- ^ statement
            -> m ()
    doWhileSt :: SourcePos -- ^ pos of expr
              -> m expr -- ^ expr
              -> m () -- ^ st
              -> m ()
    doVoidReturn :: SourcePos -- ^ pos of return
                 -> m ()
    doReturn :: m expr -- ^ return value
             -> m ()
    doBreakSt :: SourcePos
              -> m ()
    doContinueSt :: SourcePos
                 -> m ()
    doAssignSt :: SourcePos -- ^ location of loc
               -> Assigner m expr -- ^ loc
               -> AssignOp
               -> SourcePos -- ^ location of expr
               -> m expr
               -> m ()
    doBinOp :: SourcePos -- ^ location of op
            -> String -- ^ symbol for op
            -> SourcePos -- ^ location of expr1
            -> m expr
            -> SourcePos -- ^ location of expr2
            -> m expr
            -> m expr
    doUnaryOp :: SourcePos -- ^ location of op
              -> String -- ^ symbol for op
              -> SourcePos -- ^ location of expr
              -> m expr
              -> m expr
    doLiteral :: SourcePos
              -> TokenType
              -> String
              -> m expr
    doIntLiteral :: SourcePos
                 -> Int64
                 -> m expr
    doScalarLocation :: SourcePos
                     -> String
                     -> Assigner m expr
    doArrayLocation :: SourcePos
                    -> String
                    -> SourcePos
                    -> m expr
                    -> Assigner m expr
    doNormalMethod :: SourcePos
                   -> String
                   -> [m expr]
                   -> m expr
    doCalloutMethod :: SourcePos
                    -> String
                    -> [Either String (m expr)]
                    -> m expr

    
    runDProgram :: DProgram -> m ()
    runDProgram (DProgram pos fdecls mdecls)
        = doDProgram pos
          (concatMap runFieldDecl fdecls)
          (map runMethodDecl mdecls)
    
    runFieldDecl :: FieldDecl -> [m ()]
    runFieldDecl (FieldDecl pos t vars)
        = map checkvar vars
        where
          checkvar (PlainVar tok)
              = doFieldScalar (tokenPos tok) t (tokenString tok)
          checkvar (ArrayVar tok len)
              = doFieldArray (tokenPos tok) t (tokenString tok) len
    
    runMethodDecl :: MethodDecl -> m ()
    runMethodDecl (MethodDecl pos t tok args st)
        = doMethodDecl pos t fpos name (map getMArg args) mst
        where
              getMArg (MethodArg t tok')
                  = do arg <- getMethodArg (tokenPos tok') t (tokenString tok')
                       return (tokenString tok', arg)
              mst = runStatement st
              fpos = tokenPos tok
              name = tokenString tok
    
    runStatement :: Statement -> m ()
    runStatement st
        = case st of
            Block pos vdecls sts ->
                doBlock pos
                  (concatMap runVarDecl vdecls)
                  (map runStatement sts)
                where runVarDecl (VarDecl _ t vars)
                          = [doVarDecl (tokenPos v) t (tokenString v)
                             | v <- vars]
            IfSt pos expr cst mast ->
                doIfSt (getNodePos expr)
                  (runExpr expr)
                  (runStatement cst)
                  (runStatement <$> mast)
            ForSt pos tok start end st ->
                doForSt
                  (tokenPos tok) (tokenString tok)
                  (getNodePos start) (runExpr start)
                  (getNodePos end) (runExpr end)
                  (runStatement st)
            WhileSt pos expr st ->
                doWhileSt
                  (getNodePos expr) (runExpr expr)
                  (runStatement st)
            ReturnSt pos mexpr ->
                case mexpr of
                  Nothing -> doVoidReturn pos
                  Just expr -> doReturn (runExpr expr)
            BreakSt pos -> doBreakSt pos
            ContinueSt pos -> doContinueSt pos
            ExprSt ex -> runExpr ex >> return ()
            AssignSt pos loc assop ex ->
                doAssignSt
                  pos (runLocation loc)
                  assop
                  (getNodePos ex) (runExpr ex)
    
    runExpr :: Expr -> m expr
    runExpr expr 
      = case expr of
          BinaryOp pos e1 tok e2 ->
              doBinOp
                  (tokenPos tok) (tokenString tok)
                  (getNodePos e1) (runExpr e1)
                  (getNodePos e2) (runExpr e2)
          UnaryOp pos tok expr ->
              doUnaryOp
                  (tokenPos tok) (tokenString tok)
                  (getNodePos expr) (runExpr expr)
          ExprLiteral pos tok ->
              doLiteral (tokenPos tok) (tokenType tok) (tokenString tok)
          ExprIntLiteral pos i -> doIntLiteral pos i
          LoadLoc pos loc ->
              let (v,_) = runLocation loc
              in v
          ExprMethod pos call ->
              runMethod call
              
    runLocation :: DLocation -> Assigner m expr
    runLocation loc
        = case loc of
            PlainLocation pos tok ->
                doScalarLocation pos (tokenString tok)
            ArrayLocation pos tok expr ->
                doArrayLocation
                   pos (tokenString tok)
                   (getNodePos expr) (runExpr expr)
    
    runMethod :: MethodCall -> m expr
    runMethod meth
        = case meth of
            NormalMethod pos tok args ->
              doNormalMethod pos (tokenString tok) (map runExpr args)
            CalloutMethod pos tok args ->
              doCalloutMethod pos (tokenString tok) (map runCArg args)
                where runCArg a
                          = case a of
                              CArgString s -> Left $ tokenString s
                              CArgExpr ex -> Right $ runExpr ex
            

