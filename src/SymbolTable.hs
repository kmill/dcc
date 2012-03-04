{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, FlexibleContexts #-}

module SymbolTable where

import AST
import qualified Data.Map as Map
import Data.Int
import Text.PrettyPrint.HughesPJ

data SymbolEnv = SymbolEnv
    { symbolBindings :: Map.Map String SymbolTerm 
    , parentEnv :: Maybe SymbolEnv
    } 
instance Show SymbolEnv where 
    show s = "Symbols: " ++ (show $ Map.assocs $ symbolBindings s)

data SymbolTerm = Term SourcePos SymbolType
                | MethodTerm SourcePos (Maybe SymbolType)

instance Show SymbolTerm where 
    show (Term pos t) = show t
    show (MethodTerm pos (Just t)) = show t ++ " Method"
    show (MethodTerm pos Nothing) = "Void Method"

data SymbolType = SInt | SBool | SArray SymbolType Int64

instance Show SymbolType where
    show SInt = "Int"
    show SBool = "Bool"
    show (SArray t len) = show t ++ " Array"

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


data HDProgram = HDProgram SymbolEnv SourcePos [HFieldDecl] [HMethodDecl]
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

makeHybridAST :: DProgram -> HDProgram 
makeHybridAST p = createHybridAST emptyEnv p


instance Show HDProgram where
    show = render . pp

class HybridAST a b | a -> b where 
    createHybridAST :: SymbolEnv -> a -> b

instance HybridAST DProgram HDProgram where
    createHybridAST e (DProgram pos fields methods) 
        = HDProgram eNew pos (map (createHybridAST e) fields) (map (createHybridAST e) methods)
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
    createHybridAST e (Block pos vars sts)
        = HBlock eNew pos varDecls' sts'
        where eNew = extendEnv (concatMap varDeclToSTerms vars) e
              varDecls' = map (createHybridAST eNew) vars
              sts' = map (createHybridAST eNew) sts
    createHybridAST e (IfSt pos expr st maybeElse )
        = HIfSt e pos expr' (createHybridAST e st) hybridElse
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
    createHybridAST e (ExprLiteral pos tok)
        = case (tokenType tok) of
            CharLiteral -> HExprCharLiteral e pos x
                where [x] = str
            StringLiteral -> HExprStringLiteral e pos str
            BooleanLiteral -> HExprBoolLiteral e pos (str == "true")
            _ -> error "OH NO!"
          where str = tokenString tok
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

instance PP HDProgram where
    pp (HDProgram e pos fields methods) 
        = text "Program" <+> (text $ show pos) 
          $$ (text $ show e)
          $$ (nest 3 $ vcat [pp f | f <- fields])
          $$ (nest 3 $ vcat [pp m | m <- methods])

instance PP HFieldDecl where 
    pp (HFieldDecl e pos t vars) 
       = text "field" <+> (pp t)
         <+> (nest 3 $ vcat [pp v | v <- vars])
         <+> (pp pos)

instance PP HFieldVar where
    pp (HPlainVar e t) = text $ tokenString t
    pp (HArrayVar e t l) = (text $ tokenString t) <> brackets (text $ show l)

instance PP HMethodDecl where
    pp (HMethodDecl e pos t tok args st)
        = text "methoddecl" <+> (pp t) <+> (text $ tokenString tok) 
           <> parens (hsep $ punctuate comma [pp a | a <- args])
           <+> (pp pos) <+> (text $ show e)
           $+$ (nest 3 (pp st))

instance PP HMethodArg where
    pp (HMethodArg e t tok) = (pp t) <+> (text $ tokenString tok)

instance PP HStatement where
    pp (HBlock e _ vds ss)
        = (text $ show e)
           $$ (nest 0 $ vcat $ map pp vds)
           $+$ (nest 0 $ vcat $ map pp ss)
    pp (HIfSt env pos e cs mas)
       = text "if" <+> (pp e) <+> (pp pos)
         $+$ (nest 3 $ pp cs)
         $+$ (case mas of
               Just as -> text "else" $+$ (nest 3 $ pp as)
               Nothing -> empty)
    pp (HForSt env pos t s e st)
       = text "for(" <> (text $ tokenString t) 
         <+> text "=" <+> (pp s) <> text ";"
         <+> (pp e) <> text ")" <+> (pp pos) <+> (text $ show env)
         $+$ (nest 3 $ pp st)
    pp (HWhileSt env pos e st)
       = text "while" <+> (pp e) <+> (pp pos)
         $+$ (nest 3 $ pp st)
    pp (HReturnSt env pos me)
       = case me of
           Just e -> text "return" <+> (pp e) <+> (pp pos)
           Nothing -> text "return" <+> (pp pos)
    pp (HBreakSt env pos) = text "break" <+> (pp pos)
    pp (HContinueSt env pos) = text "continue" <+> (pp pos)
    pp (HExprSt env e) = pp e <+> (pp $ getNodePos e)
    pp (HAssignSt env pos loc op e)
       = text "assign"
         <+> (pp loc) <+> (pp op)
         <+> (pp e) <+> (pp pos)

instance PP HDLocation where
    pp (HPlainLocation env _ t) = text $ tokenString t
    pp (HArrayLocation env _ t e) = (text $ tokenString t)
                                 <> brackets (pp e)

instance PP HVarDecl where
    pp (HVarDecl env pos t vars)
        = text "var" <+> pp t
          <+> (nest 3 $ vcat [text $ tokenString v | v <- vars])
          <+> (pp pos)

instance PP HMethodCall where
    pp (HNormalMethod env _ t exps)
       = (text $ tokenString t)
         <> parens (hsep (punctuate (text ",") $ map pp exps))
    pp (HCalloutMethod env _ t exps)
       = (text "callout")
         <> parens (hsep (punctuate (text ",") $
                    [text $ tokenString t] ++ (map pp exps)))

instance PP HCalloutArg where
    pp (HCArgExpr env e) = pp e
    pp (HCArgString env t) = text $ show $ tokenString t

instance PP HExpr where
    pp (HBinaryOp env _ e t e2)
        = parens $ pp e <+> (text $ tokenString t) <+> pp e2
    pp (HUnaryOp env _ t e)
        = (text $ tokenString t) <> (pp e)
    pp (HExprBoolLiteral env _ b)
       = text $ show b
    pp (HExprIntLiteral env _ i)
       = text $ show i
    pp (HExprCharLiteral env _ c)
       = text $ show c
    pp (HExprStringLiteral env _ s)
       = text $ s
    pp (HLoadLoc env _ loc) = pp loc
    pp (HExprMethod env _ mc) = pp mc

instance ASTNodePos HExpr where
    getNodePos (HBinaryOp _ pos _ _ _) = pos
    getNodePos (HUnaryOp _ pos _ _) = pos
    getNodePos (HExprBoolLiteral _ pos _) = pos
    getNodePos (HExprCharLiteral _ pos _) = pos
    getNodePos (HExprStringLiteral _ pos _) = pos
    getNodePos (HExprIntLiteral _ pos _) = pos
    getNodePos (HLoadLoc _ pos _) = pos
    getNodePos (HExprMethod _ pos _) = pos