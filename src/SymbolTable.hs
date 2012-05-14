{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, FlexibleContexts #-}

-- | This is a definition of the Hybrid AST used for Code Generation. The module
-- also includes a way to pretty print the Hybrid AST

module SymbolTable where

import AST
import qualified Data.Map as Map
import Data.Int
import Control.Monad
import Text.PrettyPrint.HughesPJ

-- | SymbolEnv is a lightweight Symbol Table Component. 
-- It consists of a map mapping names to symbol terms and a 
-- reference to a parent SymbolEnv
data SymbolEnv a = SymbolEnv
    { symbolBindings :: Map.Map String SymbolTerm 
    , parentEnv :: Maybe (SymbolEnv a)
    , customValue :: a
    } 
-- SymbolEnv's should just be represented as an association list
instance Show (SymbolEnv a) where 
    show s = "Symbols: " ++ (show $ Map.assocs $ symbolBindings s)

instance PP (SymbolEnv a) where
    pp env = text "env = {"
             <> ((vcat [text (k ++ " :: " ++ show v)
                         | (k,v) <- Map.assocs $ symbolBindings env])
                 <> text "}")

-- Symbols can either be variables or methods
data SymbolTerm = Term SourcePos SymbolType
                | MethodTerm SourcePos (Maybe SymbolType)

termSize :: SymbolTerm -> Int64 
termSize (Term _ t) = typeSize t
termSize (MethodTerm _ _) = 0


instance Show SymbolTerm where 
    show (Term pos t) = show t
    show (MethodTerm pos (Just t)) = show t ++ " Method"
    show (MethodTerm pos Nothing) = "Void Method"

data SymbolType = SInt | SBool | SArray SymbolType Int64

typeSize :: SymbolType -> Int64
typeSize SInt = 8
typeSize SBool = 8
typeSize (SArray t len) = len*(typeSize t)

instance Show SymbolType where
    show SInt = "Int"
    show SBool = "Bool"
    show (SArray t len) = show t ++ " Array"

---
--- Functions for populating SymbolEnvs 
---

changeChildEnv :: (a -> b) -> (SymbolEnv b) -> (SymbolEnv a) -> (SymbolEnv b)
changeChildEnv f newParent env = SymbolEnv { symbolBindings = symbolBindings env
                                      , parentEnv = Just newParent
                                      , customValue = f $ customValue env }
                                        

emptyEnv :: a -> (SymbolEnv a)
emptyEnv custom = SymbolEnv { symbolBindings = Map.empty
                            , parentEnv = Nothing
                            , customValue = custom
                            } 

-- Add a single binding to the given SymbolEnv
envBind :: String -> SymbolTerm -> (SymbolEnv a) -> (SymbolEnv a)
envBind name val senv = senv { symbolBindings=Map.insert name val e}
    where e = symbolBindings senv

-- Add a list of bindings to the given SymbolEnv
envBindMany :: [(String, SymbolTerm)] -> SymbolEnv a -> SymbolEnv a
envBindMany pairs e = e { symbolBindings= Map.union oldMap (Map.fromList pairs) }
    where oldMap = symbolBindings e

-- Create an empty child SymbolEnv and attach it to the parent env
deriveEnv :: (a -> a) -> SymbolEnv a -> SymbolEnv a
deriveEnv f e = SymbolEnv { symbolBindings = Map.empty
                          , parentEnv = Just e
                          , customValue = f $ customValue e }

-- Create a child SymbolEnv with the given bindings and attach it to the parent env
extendEnv :: (a -> a) -> [(String, SymbolTerm)] -> SymbolEnv a -> SymbolEnv a
extendEnv f pairs e = SymbolEnv { symbolBindings = Map.fromList pairs
                                , parentEnv = Just e
                                , customValue = f $ customValue e}

--- 
--- Functions for retrieving data from SymbolEnvs
---

envLookup :: String -> (SymbolEnv a) -> Maybe SymbolTerm
envLookup name senv = Map.lookup name bindings 
                      `mplus` ((parentEnv senv) >>= envLookup name)
    where bindings = symbolBindings senv 

---
--- The Hybrid AST Data
--- Designed to mimic the AST Data in AST.hs
--- but with references to relevant SymbolEnvs
---

data HDProgram a = HDProgram (SymbolEnv a) SourcePos [(HFieldDecl a)] [(HMethodDecl a)]
data HFieldDecl a = HFieldDecl (SymbolEnv a) SourcePos DType [(HFieldVar a)]
data HFieldVar a = HPlainVar (SymbolEnv a) SourcePos Token
                 | HArrayVar (SymbolEnv a) SourcePos Token Int64
data HMethodDecl a = HMethodDecl (SymbolEnv a) SourcePos MethodType Token [(HMethodArg a)] (HStatement a)
data HMethodArg a = HMethodArg (SymbolEnv a) DType Token
data HStatement a = HBlock (SymbolEnv a) SourcePos [(HVarDecl a)] [(HStatement a)]
                  | HIfSt (SymbolEnv a) SourcePos (HExpr a) (HStatement a) (Maybe (HStatement a))
                  | HForSt (SymbolEnv a) SourcePos Token (HExpr a) (HExpr a) (HStatement a)
                  | HWhileSt (SymbolEnv a) SourcePos (HExpr a) (HStatement a)
                  | HReturnSt (SymbolEnv a) SourcePos (Maybe (HExpr a))
                  | HBreakSt (SymbolEnv a) SourcePos
                  | HContinueSt (SymbolEnv a) SourcePos
                  | HExprSt (SymbolEnv a) (HExpr a)
                  | HAssignSt (SymbolEnv a) SourcePos (HDLocation a) AssignOp (HExpr a)
data HDLocation a = HPlainLocation (SymbolEnv a) SourcePos Token
                  | HArrayLocation (SymbolEnv a) SourcePos Token (HExpr a)
data HVarDecl a = HVarDecl (SymbolEnv a) SourcePos DType [Token]
data HMethodCall a = HNormalMethod (SymbolEnv a) SourcePos Token [(HExpr a)]
                   | HCalloutMethod (SymbolEnv a) SourcePos Token [(HCalloutArg a)]
data HCalloutArg a = HCArgExpr (SymbolEnv a) (HExpr a)
                   | HCArgString (SymbolEnv a) Token
-- Note, the HExpr type defines a few more constructors corresponding to specific literal types
-- The createHybridAST method will convert string values from tokens to the appropriate literal type and value
data HExpr a = HBinaryOp (SymbolEnv a) SourcePos (HExpr a) Token (HExpr a)
             | HUnaryOp (SymbolEnv a) SourcePos Token (HExpr a)
             | HExprBoolLiteral (SymbolEnv a) SourcePos Bool 
             | HExprIntLiteral (SymbolEnv a) SourcePos Int64
             | HExprCharLiteral (SymbolEnv a) SourcePos Char
             | HExprStringLiteral (SymbolEnv a) SourcePos String
             | HLoadLoc (SymbolEnv a) SourcePos (HDLocation a)
             | HExprMethod (SymbolEnv a) SourcePos (HMethodCall a)


---
--- Functions for creating SymbolEnv bindings from AST node data
---

fieldDeclToSTerms :: FieldDecl -> [(String, SymbolTerm)]
fieldDeclToSTerms (FieldDecl pos t decls) = map (fieldVarToSTerm t) decls

fieldVarToSTerm :: DType -> FieldVar -> (String, SymbolTerm)
fieldVarToSTerm t (PlainVar pos tok) 
    = (tokenString tok, Term (tokenPos tok) (dTypeToSType t))
fieldVarToSTerm t (ArrayVar pos tok (Just len))
    = (tokenString tok, Term (tokenPos tok) (SArray (dTypeToSType t) len) )
fieldVarToSTerm _ _ = error "fieldVarToSTerm: Semantic check didn't find out-of-bounds int"

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


-- The top level function that converts an AST to a Hybrid AST
makeHybridAST :: DProgram -> (HDProgram Int) 
makeHybridAST p = createHybridAST (emptyEnv 0) p

-- | This instance just defers to 'PP' and renders
instance Show (HDProgram a) where
    show = render . pp

-- | The 'HybridAST' class is for converting AST nodes into Hybrid AST nodes
class HybridAST a b c |  b -> c where 
    createHybridAST :: SymbolEnv c -> a -> b

--- 
--- HybridAST instances
---

instance HybridAST DProgram (HDProgram Int) Int where
    createHybridAST e (DProgram pos fields methods) 
        = HDProgram eNew pos
          (map (createHybridAST eNew) fields)
          (map (createHybridAST eNew) methods)
          where eNew = envBindMany methodList (envBindMany fieldList e) 
                fieldList = concatMap fieldDeclToSTerms fields
                methodList = map methodDeclToSTerm methods

instance HybridAST FieldDecl (HFieldDecl Int) Int where
    createHybridAST e (FieldDecl pos t vars)
        = HFieldDecl e pos t $ map (createHybridAST e) vars

instance HybridAST FieldVar (HFieldVar Int) Int where
    createHybridAST e (PlainVar pos tok) = HPlainVar e pos tok
    createHybridAST e (ArrayVar pos tok (Just len)) = HArrayVar e pos tok len 
    createHybridAST _ _ = error "createHybridAST HFieldVar: out-of-bounds length"

instance HybridAST MethodDecl (HMethodDecl Int) Int where
    createHybridAST e (MethodDecl pos t tok args st) 
        = HMethodDecl eNew pos t tok
          (map (createHybridAST eNew) args)
          (createHybridAST eNew st)
        where eNew = extendEnv (+1) (map methodArgToSTerm args) e 

instance HybridAST MethodArg (HMethodArg Int) Int where
    createHybridAST e (MethodArg t tok) = HMethodArg e t tok

instance HybridAST VarDecl (HVarDecl Int) Int where 
    createHybridAST e (VarDecl pos t toks) = HVarDecl e pos t toks

instance HybridAST Statement (HStatement Int) Int where
    createHybridAST e (Block pos vars sts)
        = HBlock eNew pos varDecls' sts'
        where eNew = extendEnv (+1) (concatMap varDeclToSTerms vars) e
              varDecls' = map (createHybridAST eNew) vars
              sts' = map (createHybridAST eNew) sts
    createHybridAST e (IfSt pos expr st maybeElse )
        = HIfSt e pos expr' (createHybridAST e st) hybridElse
        where hybridElse = maybeElse >>= (Just . (createHybridAST e) )
              expr' = createHybridAST e expr
    createHybridAST e (ForSt pos tok expr1 expr2 st)
        = HForSt eNew pos tok expr1' expr2' (createHybridAST eNew st)
        where eNew = envBind (tokenString tok) (Term (tokenPos tok) SInt) (deriveEnv (+1) e)
              expr1' = createHybridAST eNew expr1
              expr2' = createHybridAST eNew expr2
    createHybridAST e (WhileSt pos expr st)
        = HWhileSt e pos (createHybridAST e expr) (createHybridAST e st)
    createHybridAST e (ReturnSt pos maybeExpr)
        = HReturnSt e pos maybeExpr'
        where maybeExpr' = maybeExpr >>= (Just . (createHybridAST e) )
    createHybridAST e (BreakSt pos) = HBreakSt e pos 
    createHybridAST e (ContinueSt pos) = HContinueSt e pos
    createHybridAST e (ExprSt expr) = HExprSt e  (createHybridAST e expr)
    createHybridAST e (AssignSt pos loc op expr) = HAssignSt e pos (createHybridAST e loc) op (createHybridAST e expr)

instance HybridAST Expr (HExpr Int) Int where 
    createHybridAST e (BinaryOp pos expr1 tok expr2) = HBinaryOp e pos (createHybridAST e expr1) tok (createHybridAST e expr2)
    createHybridAST e (UnaryOp pos tok expr) = HUnaryOp e pos tok (createHybridAST e expr) 
    createHybridAST e (ExprLiteral pos tok)
        -- Here is where conversion of token strings to proper values happens
        = case (tokenType tok) of
            CharLiteral -> HExprCharLiteral e pos x
                where [x] = str
            StringLiteral -> HExprStringLiteral e pos str
            BooleanLiteral -> HExprBoolLiteral e pos (str == "true")
            _ -> error "OH NO!"
          where str = tokenString tok
    createHybridAST e (ExprIntLiteral pos (Just num)) = HExprIntLiteral e pos num
    createHybridAST e (ExprIntLiteral _ _) = error "createHybridAST ExprIntLiteral out of bounds"
    createHybridAST e (LoadLoc pos loc) = HLoadLoc e pos (createHybridAST e loc)
    createHybridAST e (ExprMethod pos call) = HExprMethod e pos (createHybridAST e call) 
                                                
instance HybridAST DLocation (HDLocation Int) Int where
    createHybridAST e (PlainLocation pos tok) = HPlainLocation e pos tok
    createHybridAST e (ArrayLocation pos tok expr) = HArrayLocation e pos tok (createHybridAST e expr) 

instance HybridAST MethodCall (HMethodCall Int) Int where 
    createHybridAST e (NormalMethod pos tok exprs) = HNormalMethod e pos tok (map (createHybridAST e) exprs)
    createHybridAST e (CalloutMethod pos tok args) = HCalloutMethod e pos tok (map (createHybridAST e) args) 

instance HybridAST CalloutArg (HCalloutArg Int) Int where
    createHybridAST e (CArgExpr expr) = HCArgExpr e (createHybridAST e expr) 
    createHybridAST e (CArgString tok) = HCArgString e tok

--- 
---
---

transformHDProgram :: (Maybe (SymbolEnv b) -> SymbolEnv a -> SymbolEnv b) -> HDProgram a -> HDProgram b
transformHDProgram f program@(HDProgram env pos fields methods) = HDProgram eNew pos fields' methods'
    where eNew = f Nothing env
          fields' = map (transformHFieldDecl eNew) fields
          methods' = map (transformHMethodDecl f eNew) methods

transformHFieldDecl :: SymbolEnv b -> HFieldDecl a -> HFieldDecl b
transformHFieldDecl eNew (HFieldDecl _ pos t vars) = HFieldDecl eNew pos t vars'
    where vars' = map (transformHFieldVar eNew) vars

transformHFieldVar :: SymbolEnv b -> HFieldVar a -> HFieldVar b
transformHFieldVar eNew (HPlainVar _ pos tok) = HPlainVar eNew pos tok
transformHFieldVar eNew (HArrayVar _ pos tok len) = HArrayVar eNew pos tok len

transformHMethodDecl :: (Maybe (SymbolEnv b) -> SymbolEnv a -> SymbolEnv b) -> SymbolEnv b -> HMethodDecl a -> HMethodDecl b
transformHMethodDecl f eParent (HMethodDecl env pos t tok args st) = HMethodDecl eNew pos t tok args' st'
    where eNew = f (Just eParent) env 
          args' = map (transformHMethodArg eNew) args
          st' = transformHStatement f eNew st

transformHMethodArg :: SymbolEnv b -> HMethodArg a -> HMethodArg b
transformHMethodArg eNew (HMethodArg _ t tok) = HMethodArg eNew t tok

transformHStatement :: (Maybe (SymbolEnv b) -> SymbolEnv a -> SymbolEnv b) -> SymbolEnv b -> HStatement a -> HStatement b
transformHStatement f eParent (HBlock env pos vars sts) = HBlock eNew pos vars' sts'
    where eNew = f (Just eParent) env
          vars' = map (transformHVarDecl eNew) vars
          sts' = map (transformHStatement f eNew) sts
transformHStatement f eParent (HIfSt env pos expr st1 maybeSt) = HIfSt eParent pos expr' st1' maybeSt'
    where expr' = transformHExpr eParent expr 
          st1' = transformHStatement f eParent st1
          maybeSt' = maybeSt >>= (return . (transformHStatement f eParent) )
transformHStatement f eParent (HForSt env pos tok expr1 expr2 st) = HForSt eNew pos tok expr1' expr2' st'
    where eNew = f (Just eParent) env
          expr1' = transformHExpr eNew expr1
          expr2' = transformHExpr eNew expr2
          st' = transformHStatement f eNew st
transformHStatement f eParent (HWhileSt env pos expr st) = HWhileSt eParent pos expr' st'
    where expr' = transformHExpr eParent expr
          st' = transformHStatement f eParent st
transformHStatement f eParent (HReturnSt env pos maybeExpr) = HReturnSt eParent pos maybeExpr'
    where maybeExpr' = maybeExpr >>= (return . (transformHExpr eParent) )
transformHStatement f eParent (HBreakSt env pos) = HBreakSt eParent pos 
transformHStatement f eParent (HContinueSt env pos) = HContinueSt eParent pos
transformHStatement f eParent (HExprSt env expr) = HExprSt eParent expr'
    where expr' = transformHExpr eParent expr
transformHStatement f eParent (HAssignSt env pos loc op expr) = HAssignSt eParent pos loc' op expr'
    where loc' = transformHDLocation eParent loc
          expr' = transformHExpr eParent expr

transformHDLocation :: SymbolEnv b -> HDLocation a -> HDLocation b
transformHDLocation eNew (HPlainLocation _ pos tok) = HPlainLocation eNew pos tok
transformHDLocation eNew (HArrayLocation _ pos tok expr) = HArrayLocation eNew pos tok expr'
    where expr' = transformHExpr eNew expr

transformHVarDecl :: SymbolEnv b -> HVarDecl a -> HVarDecl b 
transformHVarDecl eNew (HVarDecl _ pos t toks) = HVarDecl eNew pos t toks

transformHMethodCall :: SymbolEnv b -> HMethodCall a -> HMethodCall b 
transformHMethodCall eNew (HNormalMethod _ pos tok exprs) = HNormalMethod eNew pos tok exprs'
    where exprs' = map (transformHExpr eNew) exprs
transformHMethodCall eNew (HCalloutMethod _ pos tok args) = HCalloutMethod eNew pos tok args'
    where args' = map (transformHCalloutArg eNew) args

transformHCalloutArg :: SymbolEnv b -> HCalloutArg a -> HCalloutArg b 
transformHCalloutArg eNew (HCArgExpr _ expr) = HCArgExpr eNew expr'
    where expr' = transformHExpr eNew expr
transformHCalloutArg eNew (HCArgString _ tok) = HCArgString eNew tok

transformHExpr :: SymbolEnv b -> HExpr a -> HExpr b 
transformHExpr eNew (HBinaryOp _ pos expr1 tok expr2) = HBinaryOp eNew pos expr1' tok expr2'
    where expr1' = transformHExpr eNew expr1
          expr2' = transformHExpr eNew expr2
transformHExpr eNew (HUnaryOp _ pos tok expr) = HUnaryOp eNew pos tok expr'
    where expr' = transformHExpr eNew expr
transformHExpr eNew (HExprBoolLiteral _ pos b) = HExprBoolLiteral eNew pos b 
transformHExpr eNew (HExprIntLiteral _ pos i) = HExprIntLiteral eNew pos i
transformHExpr eNew (HExprCharLiteral _ pos c) = HExprCharLiteral eNew pos c
transformHExpr eNew (HExprStringLiteral _ pos s) = HExprStringLiteral eNew pos s
transformHExpr eNew (HLoadLoc _ pos loc) = HLoadLoc eNew pos loc'
    where loc' = transformHDLocation eNew loc
transformHExpr eNew (HExprMethod _ pos call) = HExprMethod eNew pos call'
    where call' = transformHMethodCall eNew call




---
--- PP instances
--- Should be nearly idential to instances in AST.hs with the addition of printing SymbolEnvs 
--- where new symbols are defined
--- 

instance PP (HDProgram a) where
    pp (HDProgram env pos fields methods) 
        = text "Program" <+> (text $ show pos) 
          $+$ (pp env)
          $+$ (nest 3 $ vcat [pp f | f <- fields])
          $+$ (nest 3 $ vcat [pp m | m <- methods])

instance PP (HFieldDecl a) where 
    pp (HFieldDecl e pos t vars) 
       = text "field" <+> (pp t)
         <+> (nest 3 $ vcat [pp v | v <- vars])
         <+> (pp pos)

instance PP (HFieldVar a) where
    pp (HPlainVar e pos t) = text $ tokenString t
    pp (HArrayVar e pos t l) = (text $ tokenString t) <> brackets (text $ show l)

instance PP (HMethodDecl a) where
    pp (HMethodDecl env pos t tok args st)
        = text "methoddecl" <+> (pp t) <+> (text $ tokenString tok) 
           <> parens (hsep $ punctuate comma [pp a | a <- args])
           <+> (pp pos)
           $+$ (pp env)
           $+$ (pp st)

instance PP (HMethodArg a) where
    pp (HMethodArg e t tok) = (pp t) <+> (text $ tokenString tok)

instance PP (HStatement a) where
    pp (HBlock env _ vds ss)
        = --(text $ "block") $+$
           (nest 3 $ pp env)
           $+$ (nest 3 $ vcat $ map pp ss)
    pp (HIfSt env pos e cs mas)
       = text "if" <+> (pp e) <+> (pp pos)
         $+$ (pp cs)
         $+$ (case mas of
               Just as -> text "else" $+$ (pp as)
               Nothing -> empty)
    pp (HForSt env pos t s e st)
       = text "for(" <> (text $ tokenString t) 
         <+> text "=" <+> (pp s) <> text ";"
         <+> (pp e) <> text ")" <+> (pp pos) <+> (text $ show env)
         $+$ (pp st)
    pp (HWhileSt env pos e st)
       = text "while" <+> (pp e) <+> (pp pos)
         $+$ (pp st)
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

instance PP (HDLocation a) where
    pp (HPlainLocation env _ t) = text $ tokenString t
    pp (HArrayLocation env _ t e) = (text $ tokenString t)
                                 <> brackets (pp e)

instance PP (HVarDecl a) where
    pp (HVarDecl env pos t vars)
        = text "var" <+> pp t
          <+> (nest 3 $ vcat [text $ tokenString v | v <- vars])
          <+> (pp pos)

instance PP (HMethodCall a) where
    pp (HNormalMethod env _ t exps)
       = (text $ tokenString t)
         <> parens (hsep (punctuate (text ",") $ map pp exps))
    pp (HCalloutMethod env _ t exps)
       = (text "callout")
         <> parens (hsep (punctuate (text ",") $
                    [text $ tokenString t] ++ (map pp exps)))

instance PP (HCalloutArg a) where
    pp (HCArgExpr env e) = pp e
    pp (HCArgString env t) = text $ show $ tokenString t

instance PP (HExpr a) where
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

-- | This instance is so we can pretty print HExprs
instance ASTNodePos (HExpr a) where
    getNodePos (HBinaryOp _ pos _ _ _) = pos
    getNodePos (HUnaryOp _ pos _ _) = pos
    getNodePos (HExprBoolLiteral _ pos _) = pos
    getNodePos (HExprCharLiteral _ pos _) = pos
    getNodePos (HExprStringLiteral _ pos _) = pos
    getNodePos (HExprIntLiteral _ pos _) = pos
    getNodePos (HLoadLoc _ pos _) = pos
    getNodePos (HExprMethod _ pos _) = pos