-- | This is a definition of the AST for the decaf language.  The
-- module includes a way to pretty print the AST as well.

module AST ( PP(..)
           , SourcePos
           , showPos
           , DProgram(..) 
           , FieldDecl(..)
           , FieldVar(..)
           , MethodDecl(..)
           , MethodType(..)
           , MethodArg(..)
           , Statement(..)
           , DLocation(..)
           , VarDecl(..)
           , DType(..)
           , AssignOp(..)
           , MethodCall(..)
           , CalloutArg(..)
           , Expr(..)
           , Token(..)
           , TokenType(..)
           , ASTNodePos(..)
           )
    where

import Scanner(Token(..),TokenType(..))
import Text.ParserCombinators.Parsec
import Text.PrettyPrint.HughesPJ
import Data.Int

-- | The 'PP' class is for pretty printing objects into 'Doc's.
class PP a where
    pp :: a -> Doc

-- | This prints out 'SourcePos' in a more column-friendly manner.
showPos :: SourcePos -> String
showPos pos = "line " ++ (show $ sourceLine pos)
              ++ ", col " ++ (show $ sourceColumn pos)

---
--- AST data
---

data DProgram = DProgram !SourcePos [FieldDecl] [MethodDecl]
data FieldDecl = FieldDecl !SourcePos DType [FieldVar]
data FieldVar = PlainVar SourcePos Token
              | ArrayVar SourcePos Token Int64
data MethodDecl = MethodDecl !SourcePos MethodType Token [MethodArg] Statement
data MethodType = MethodReturns DType
                | MethodVoid
data MethodArg = MethodArg DType Token
data Statement = Block !SourcePos [VarDecl] [Statement]
               | IfSt !SourcePos Expr Statement (Maybe Statement)
               | ForSt !SourcePos Token Expr Expr Statement
               | WhileSt !SourcePos Expr Statement
               | ReturnSt !SourcePos (Maybe Expr)
               | BreakSt !SourcePos
               | ContinueSt !SourcePos
               | ExprSt Expr
               | AssignSt !SourcePos DLocation AssignOp Expr
data DLocation = PlainLocation !SourcePos Token
               | ArrayLocation !SourcePos Token Expr
data VarDecl = VarDecl !SourcePos DType [Token]
data DType = DInt
           | DBool
data AssignOp = Assign | IncAssign | DecAssign
data MethodCall = NormalMethod !SourcePos Token [Expr]
                | CalloutMethod !SourcePos Token [CalloutArg]
data CalloutArg = CArgExpr Expr
                | CArgString Token
data Expr = BinaryOp !SourcePos Expr Token Expr
          | UnaryOp !SourcePos Token Expr
          | ExprLiteral !SourcePos Token
          | ExprIntLiteral !SourcePos Int64
          | LoadLoc !SourcePos DLocation
          | ExprMethod !SourcePos MethodCall


-- | This class is for being able to get the position of a node in a
-- general way.  This hasn't been implemented for each of the nodes
-- yet.
class ASTNodePos a where
    getNodePos :: a -> SourcePos

instance ASTNodePos Expr where
    getNodePos (BinaryOp pos _ _ _) = pos
    getNodePos (UnaryOp pos _ _) = pos
    getNodePos (ExprLiteral pos _) = pos
    getNodePos (ExprIntLiteral pos _) = pos
    getNodePos (LoadLoc pos _) = pos
    getNodePos (ExprMethod pos _) = pos

instance ASTNodePos DProgram where 
    getNodePos (DProgram pos _ _) = pos

instance ASTNodePos FieldDecl where
    getNodePos (FieldDecl pos _ _) = pos 

instance ASTNodePos MethodDecl where
    getNodePos (MethodDecl pos _ _ _ _) = pos 

instance ASTNodePos Statement where
    getNodePos (Block pos _ _) = pos
    getNodePos (IfSt pos _ _ _) = pos
    getNodePos (ForSt pos _ _ _ _) = pos
    getNodePos (WhileSt pos _ _) = pos
    getNodePos (ReturnSt pos _) = pos
    getNodePos (BreakSt pos) = pos
    getNodePos (ContinueSt pos) = pos
    getNodePos (ExprSt e) = getNodePos e
    getNodePos (AssignSt pos _ _ _) = pos

instance ASTNodePos DLocation where
    getNodePos (PlainLocation pos _) = pos
    getNodePos (ArrayLocation pos _ _) = pos

instance ASTNodePos VarDecl where
    getNodePos (VarDecl pos _ _) = pos

instance ASTNodePos MethodCall where
    getNodePos (NormalMethod pos _ _) = pos
    getNodePos (CalloutMethod pos _ _) = pos







---
--- Displaying ASTs
---

-- | This instance just defers to 'PP' and renders.
instance Show DProgram where
    show = render . pp

---
--- PP instances
---

instance PP DProgram where
    pp (DProgram pos fields methods)
        = text "Program" <+> (text $ show pos)
          $$ (nest 3 $ vcat [pp f | f <- fields])
          $$ (nest 3 $ vcat [pp m | m <- methods])

instance PP FieldDecl where
    pp (FieldDecl pos t vars)
        = text "field" <+> (pp t)
          <+> (nest 3 $ vcat [pp v | v <- vars])
          <+> (pp pos)

instance PP FieldVar where
    pp (PlainVar pos t) = text $ tokenString t
    pp (ArrayVar pos t l) = (text $ tokenString t) <> brackets (text $ show l)

instance PP MethodDecl where
    pp (MethodDecl pos t tok args st)
        = text "methoddecl" <+> (pp t) <+> (text $ tokenString tok)
           <> parens (hsep $ punctuate comma [pp a | a <- args])
           <+> (pp pos)
           $+$ (nest 3 (pp st))

instance PP MethodType where
    pp (MethodReturns x) = pp x
    pp MethodVoid = text "void"

instance PP MethodArg where
    pp (MethodArg t tok) = (pp t) <+> (text $ tokenString tok)

instance PP SourcePos where
    pp pos
        = text " <--"
          <> (braces . text $ "line " ++ show line ++
                         ", column " ++ show column)
          where --name = sourceName pos
                line = sourceLine pos
                column = sourceColumn pos

instance PP Statement where
    pp (Block _ vds ss)
        = --(pp pos)
          (nest 0 $ vcat $ map pp vds)
          $+$ (nest 0 $ vcat $ map pp ss)
    pp (IfSt pos e cs mas)
       = text "if" <+> (pp e) <+> (pp pos)
         $+$ (nest 3 $ pp cs)
         $+$ (case mas of
               Just as -> text "else" $+$ (nest 3 $ pp as)
               Nothing -> empty)
    pp (ForSt pos t s e st)
       = text "for(" <> (text $ tokenString t)
         <+> text "=" <+> (pp s) <> text ";"
         <+> (pp e) <> text ")" <+> (pp pos)
         $+$ (nest 3 $ pp st)
    pp (WhileSt pos e st)
       = text "while" <+> (pp e) <+> (pp pos)
         $+$ (nest 3 $ pp st)
    pp (ReturnSt pos me)
       = case me of
           Just e -> text "return" <+> (pp e) <+> (pp pos)
           Nothing -> text "return" <+> (pp pos)
    pp (BreakSt pos) = text "break" <+> (pp pos)
    pp (ContinueSt pos) = text "continue" <+> (pp pos)
    pp (ExprSt e) = pp e <+> (pp $ getNodePos e)
    pp (AssignSt pos loc op e)
       = text "assign"
         <+> (pp loc) <+> (pp op)
         <+> (pp e) <+> (pp pos)

instance PP DLocation where
    pp (PlainLocation _ t) = text $ tokenString t
    pp (ArrayLocation _ t e) = (text $ tokenString t)
                                 <> brackets (pp e)

instance PP VarDecl where
    pp (VarDecl pos t vars)
        = text "var" <+> pp t
          <+> (nest 3 $ vcat [text $ tokenString v | v <- vars])
          <+> (pp pos)

instance PP DType where
    pp DInt = text "int"
    pp DBool = text "bool"

instance PP AssignOp where
    pp Assign = text "="
    pp IncAssign = text "+="
    pp DecAssign = text "-="

instance PP MethodCall where
    pp (NormalMethod _ t exps)
       = (text $ tokenString t)
         <> parens (hsep (punctuate (text ",") $ map pp exps))
    pp (CalloutMethod _ t exps)
       = (text "callout")
         <> parens (hsep (punctuate (text ",") $
                    [text $ tokenString t] ++ (map pp exps)))

instance PP CalloutArg where
    pp (CArgExpr e) = pp e
    pp (CArgString t) = text $ show $ tokenString t

instance PP Expr where
    pp (BinaryOp _ e t e2)
        = parens $ pp e <+> (text $ tokenString t) <+> pp e2
    pp (UnaryOp _ t e)
        = (text $ tokenString t) <> (pp e)
    pp (ExprLiteral _ t)
       = text $ tokenString t
    pp (ExprIntLiteral _ i)
       = text $ show i
    pp (LoadLoc _ loc) = pp loc
    pp (ExprMethod _ mc) = pp mc
