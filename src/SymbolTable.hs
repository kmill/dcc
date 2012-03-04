{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, FlexibleContexts #-}

module SymbolTable where

import AST
import qualified Data.Map as Map
import Data.Int

data SymbolEnv = SymbolEnv
    { symbolBindings :: Map.Map String SymbolTerm 
    , parentEnv :: Maybe SymbolEnv
    } 
instance Show SymbolEnv where 
    show s = "TODO: Show Symbol Environment"

data SymbolTerm = Term SourcePos SymbolType
                | MethodTerm SourcePos (Maybe SymbolType)

data SymbolType = SInt | SBool | SArray SymbolType Int64

emptyEnv :: SymbolEnv 
emptyEnv = SymbolEnv { symbolBindings = Map.empty
                     , parentEnv = Nothing
                     } 

envBind :: String -> SymbolTerm -> SymbolEnv -> SymbolEnv
envBind name val senv = senv { symbolBindings=Map.insert name val e}
    where e = symbolBindings senv

envBindMany :: [(String, SymbolTerm)] -> SymbolEnv -> SymbolEnv
envBindMany pairs e = e { symbolBindings= Map.union oldMap (Map.fromList pairs) }
    where oldMap = symbolBindings e

deriveEnv :: SymbolEnv -> SymbolEnv 
deriveEnv e = SymbolEnv { symbolBindings = Map.empty
                        , parentEnv = Just e }

extendEnv :: [(String, SymbolTerm)] -> SymbolEnv -> SymbolEnv
extendEnv pairs e = SymbolEnv { symbolBindings = Map.fromList pairs
                              , parentEnv = Just e } 


data HDProgram = HDProgram SymbolEnv SourcePos [HFieldDecl] [MethodDecl]
data HFieldDecl = HFieldDecl SymbolEnv SourcePos DType [HFieldVar]
data HFieldVar = HPlainVar SymbolEnv Token
               | HArrayVar SymbolEnv Token Int64
data HMethodDecl = HMethodDecl SymbolEnv SourcePos MethodType Token [HMethodArg] HStatement
data HMethodArg = HMethodArg SymbolEnv DType Token
data HStatement = HBlock SymbolEnv SourcePos [HVarDecl] [HStatement]
                | HIfSt SymbolEnv SourcePos HExpr HStatement (Maybe HStatement)
                | HForSt SymbolEnv SourcePos Token HExpr HExpr HStatement
                | HWhileSt SymbolEnv SourcePos HExpr HStatement
                | HReturnSt SymbolEnv SourcePos (Maybe HExpr)
                | HBreakSt SymbolEnv SourcePos
                | HContinueSt SymbolEnv SourcePos
                | HExprSt SymbolEnv HExpr
                | HAssignSt SymbolEnv SourcePos HDLocation AssignOp HExpr
data HDLocation = HPlainLocation SymbolEnv SourcePos Token
                | HArrayLocation SymbolEnv SourcePos Token HExpr
data HVarDecl = HVarDecl SymbolEnv SourcePos DType [Token]
data HMethodCall = HNormalMethod SymbolEnv SourcePos Token [HExpr]
                 | HCalloutMethod SymbolEnv SourcePos Token [HCalloutArg]
data HCalloutArg = HCArgExpr SymbolEnv HExpr
                 | HCArgString SymbolEnv Token
data HExpr = HBinaryOp SymbolEnv SourcePos HExpr Token HExpr
           | HUnaryOp SymbolEnv SourcePos Token HExpr
           | HExprBoolLiteral SymbolEnv SourcePos Bool 
           | HExprIntLiteral SymbolEnv SourcePos Int64
           | HExprCharLiteral SymbolEnv SourcePos Char
           | HExprStringLiteral SymbolEnv SourcePos String
           | HLoadLoc SymbolEnv SourcePos HDLocation
           | HExprMethod SymbolEnv SourcePos HMethodCall



fieldDeclToSTerms :: FieldDecl -> [(String, SymbolTerm)]
fieldDeclToSTerms (FieldDecl pos t decls) = map (fieldVarToSTerm t) decls

fieldVarToSTerm :: DType -> FieldVar -> (String, SymbolTerm)
fieldVarToSTerm t (PlainVar tok) 
    = (tokenString tok, Term (tokenPos tok) (dTypeToSType t))
fieldVarToSTerm t (ArrayVar tok len) 
    = (tokenString tok, Term (tokenPos tok) (SArray (dTypeToSType t) len) )

methodDeclToSTerm :: MethodDecl -> (String, SymbolTerm)
methodDeclToSTerm (MethodDecl pos t tok args _) 
    = (tokenString tok, MethodTerm pos (methodType t))
    where methodType (MethodReturns mt) = Just (dTypeToSType mt)
          methodType _ = Nothing


methodArgToSTerm :: MethodArg -> (String, SymbolTerm) 
methodArgToSTerm (MethodArg t tok) = (tokenString tok, Term (tokenPos tok) (dTypeToSType t))

varDeclToSTerms :: VarDecl -> [(String, SymbolTerm)] 
varDeclToSTerms (VarDecl pos t toks) = map (varDeclToSTerm t) toks
    where varDeclToSTerm t' tok = (tokenString tok, Term (tokenPos tok) (dTypeToSType t'))

dTypeToSType :: DType -> SymbolType
dTypeToSType DInt = SInt
dTypeToSType DBool = SBool

--convertTokenValue :: Token -> a 
--convertTokenValue Token { tokenType = IntLiteral, tokenString=s } = read s :: Int
--convertTokenValue Token { tokenType = BooleanLiteral, tokenString=s } = s == "true"

class HybridAST a b | a -> b where 
    createHybridAST :: SymbolEnv -> a -> b

instance HybridAST DProgram HDProgram where
    createHybridAST e (DProgram pos fields methods) 
        = HDProgram eNew pos (map (createHybridAST e) fields) methods
        where eNew = envBindMany methodList (envBindMany fieldList e) 
              fieldList = concatMap fieldDeclToSTerms fields
              methodList = map methodDeclToSTerm methods


instance HybridAST FieldDecl HFieldDecl where
    createHybridAST e (FieldDecl pos t vars) = HFieldDecl e pos t $ map (createHybridAST e) vars

instance HybridAST FieldVar HFieldVar where
    createHybridAST e (PlainVar tok) = HPlainVar e tok
    createHybridAST e (ArrayVar tok len) = HArrayVar e tok len 

instance HybridAST MethodDecl HMethodDecl where
    createHybridAST e (MethodDecl pos t tok args st) 
        = HMethodDecl eNew pos t tok (map (createHybridAST eNew) args) (createHybridAST eNew st)
        where eNew = extendEnv (map methodArgToSTerm args) e 

instance HybridAST MethodArg HMethodArg where
    createHybridAST e (MethodArg t tok) = HMethodArg e t tok

instance HybridAST VarDecl HVarDecl where 
    createHybridAST e (VarDecl pos t toks) = HVarDecl e pos t toks

instance HybridAST Statement HStatement where
    createHybridAST e (Block pos vars sts) = HBlock eNew pos (map (createHybridAST eNew) vars) (map (createHybridAST eNew) sts)
        where eNew = extendEnv (concatMap varDeclToSTerms vars) e
    createHybridAST e (IfSt pos expr st maybeElse ) = HIfSt e pos expr' (createHybridAST e st) hybridElse
        where hybridElse = maybeElse >>= (Just . (createHybridAST e) )
              expr' = createHybridAST e expr
    createHybridAST e (ForSt pos tok expr1 expr2 st) = HForSt eNew pos tok expr1' expr2' (createHybridAST eNew st)
        where eNew = envBind (tokenString tok) (Term (tokenPos tok) SInt) (deriveEnv e)
              expr1' = createHybridAST eNew expr1
              expr2' = createHybridAST eNew expr2
    createHybridAST e (WhileSt pos expr st) = HWhileSt e pos (createHybridAST e expr) (createHybridAST e st)
    createHybridAST e (ReturnSt pos maybeExpr) = HReturnSt e pos maybeExpr'
        where maybeExpr' = maybeExpr >>= (Just . (createHybridAST e) )
    createHybridAST e (BreakSt pos) = HBreakSt e pos 
    createHybridAST e (ContinueSt pos) = HContinueSt e pos
    createHybridAST e (ExprSt expr) = HExprSt e  (createHybridAST e expr)
    createHybridAST e (AssignSt pos loc op expr) = HAssignSt e pos (createHybridAST e loc) op (createHybridAST e expr)

instance HybridAST Expr HExpr where 
    createHybridAST e (BinaryOp pos expr1 tok expr2) = HBinaryOp e pos (createHybridAST e expr1) tok (createHybridAST e expr2)
    createHybridAST e (UnaryOp pos tok expr) = HUnaryOp e pos tok (createHybridAST e expr) 
    createHybridAST e (ExprLiteral pos tok) = case (tokenString tok) of 
                                                 "true" -> HExprBoolLiteral e pos True
                                                 "false" -> HExprBoolLiteral e pos False
                                                 x:[] -> HExprCharLiteral e pos x 
                                                 str -> HExprStringLiteral e pos str 
    createHybridAST e (ExprIntLiteral pos num) = HExprIntLiteral e pos num
    createHybridAST e (LoadLoc pos loc) = HLoadLoc e pos (createHybridAST e loc)
    createHybridAST e (ExprMethod pos call) = HExprMethod e pos (createHybridAST e call) 
                                                
instance HybridAST DLocation HDLocation where
    createHybridAST e (PlainLocation pos tok) = HPlainLocation e pos tok
    createHybridAST e (ArrayLocation pos tok expr) = HArrayLocation e pos tok (createHybridAST e expr) 

instance HybridAST MethodCall HMethodCall where 
    createHybridAST e (NormalMethod pos tok exprs) = HNormalMethod e pos tok (map (createHybridAST e) exprs)
    createHybridAST e (CalloutMethod pos tok args) = HCalloutMethod e pos tok (map (createHybridAST e) args) 

instance HybridAST CalloutArg HCalloutArg where
    createHybridAST e (CArgExpr expr) = HCArgExpr e (createHybridAST e expr) 
    createHybridAST e (CArgString tok) = HCArgString e tok