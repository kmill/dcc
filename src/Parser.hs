module Parser(runDParser) where

import Scanner
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import CLI
import Control.Applicative (Applicative, pure, (<$>), (<*>), (<*), (*>), (<$), liftA2)
import Debug.Trace

import Text.PrettyPrint.HughesPJ

-- at this stage, all parsers must return ()
type DParser a = GenParser Token DParserState a
data DParserState = DParserState

runDParser :: CompilerOpts -> String -> [Token] -> Either ParseError DProgram
runDParser opts fname input
    = runParser dprogram parseState fname input
      where parseState = DParserState

dtoken :: TokenType -> DParser Token
dtoken tt = dtoken' (\t -> tt == tokenType t) <?> (show tt)

dtoken' :: (Token -> Bool) -> DParser Token
dtoken' p = token showtok tokenPos testtok
    where showtok = show
          testtok t = if p t then Just t else Nothing

dkeyword :: String -> DParser Token
dkeyword s = dtoken' (\t -> tokenType t == Keyword && tokenString t == s)
             <?> "\"" ++ s ++ "\""

--dkeywords :: [String] -> a
dkeywords = (foldl1 (<|>)) . (map dkeyword)

class PP a where
    pp :: a -> Doc

data DProgram = DProgram SourcePos [FieldDecl] [MethodDecl]

instance Show DProgram where
    show = render . pp

instance PP DProgram where
    pp (DProgram pos fields methods)
        = text "Program" <+> (text $ show pos)
          $$ (nest 3 $ vcat [pp f | f <- fields])
          $$ (nest 3 $ vcat [pp m | m <- methods])

-- dprogram is the main entry point into the parser
dprogram :: DParser DProgram
dprogram = DProgram <$> getPosition
           <* header
           <*> many fieldDecl
           <*> many methodDecl
           <* dkeyword "}"
    where header = dkeyword "class" >> identProgram >> dkeyword "{"
          identProgram = dtoken' (\t -> Identifier == tokenType t
                                        && "Program" == tokenString t)
                          <?> "identifier \"Program\""
          

dsemi :: DParser ()
dsemi = dkeyword ";" >> return ()

dopenp :: DParser ()
dopenp = dkeyword "(" >> return ()
dclosep :: DParser ()
dclosep = dkeyword ")" >> return ()
dopensb :: DParser ()
dopensb = dkeyword "[" >> return ()
dclosesb :: DParser ()
dclosesb = dkeyword "]" >> return ()
dopenbr :: DParser ()
dopenbr = dkeyword "{" >> return ()
dclosebr :: DParser ()
dclosebr = dkeyword "}" >> return ()

dcomma :: DParser ()
dcomma = dkeyword "," >> return ()

-- fixed some kind of bug in parsec...
tLookAhead = try . lookAhead

data FieldDecl = FieldDecl SourcePos DType [FieldVar]
                 deriving Show

instance PP FieldDecl where
    pp (FieldDecl pos t vars)
        = text "field" <+> (pp t)
          <+> (nest 3 $ vcat [pp v | v <- vars])
          <+> (pp pos)

data FieldVar = PlainVar Token
              | ArrayVar Token Token
                deriving Show

instance PP FieldVar where
    pp (PlainVar t) = text $ tokenString t
    pp (ArrayVar t l) = (text $ tokenString t) <> brackets (text $ tokenString l)

fieldDecl :: DParser FieldDecl
fieldDecl = FieldDecl <$> getPosition
            <*> (try $ dtype <* -- three symbol lookahead
                         (tLookAhead $ ident >> (dsemi <|> dopensb <|> dcomma)))
            <*> (sepBy1 (arrayVar <|> plainVar) dcomma)
            <* dsemi
    where plainVar = PlainVar <$> try ident
          arrayVar = ArrayVar
                     <$> (try $ ident <* dopensb)
                     <*> (dtoken IntLiteral)
                     <* dclosesb

data MethodDecl = MethodDecl SourcePos MethodType Token [MethodArg] Statement

instance PP MethodDecl where
    pp (MethodDecl pos t tok args st)
        = text "methoddecl" <+> (pp t) <+> (text $ tokenString tok)
           <> parens (hsep $ punctuate comma [pp a | a <- args])
           <+> (pp pos)
           $+$ (nest 3 (pp st))


data MethodType = MethodReturns DType
                | MethodVoid

instance PP MethodType where
    pp (MethodReturns x) = pp x
    pp MethodVoid = text "void"

data MethodArg = MethodArg DType Token

instance PP MethodArg where
    pp (MethodArg t tok) = (pp t) <+> (text $ tokenString tok)

methodDecl :: DParser MethodDecl
methodDecl = MethodDecl <$> getPosition
             <*> do try ((MethodReturns <$> dtype)
                         <|> (MethodVoid <$ dkeyword "void"))
             <*> ident
             <*> (between dopenp dclosep $ arg `sepBy` dcomma)
             <*> block
    where arg = MethodArg
                <$> dtype
                <*> ident

data Statement = Block SourcePos [VarDecl] [Statement]
               | IfSt SourcePos Expr Statement (Maybe Statement)
               | ForSt SourcePos Token Expr Expr Statement
               | WhileSt SourcePos Expr Statement
               | ReturnSt SourcePos (Maybe Expr)
               | BreakSt SourcePos
               | ContinueSt SourcePos
               | ExprSt Expr
               | AssignSt SourcePos DLocation AssignOp Expr

instance PP SourcePos where
    pp pos
        = text " <--"
          <> (braces . text $ "line " ++ show line ++
                         ", column " ++ show column)
          where name = sourceName pos
                line = sourceLine pos
                column = sourceColumn pos

instance PP Statement where
    pp (Block pos vds ss)
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
         <+> (pp loc) <+> (text $ show op)
         <+> (pp e) <+> (pp pos)

data DLocation = PlainLocation SourcePos Token
               | ArrayLocation SourcePos Token Expr

instance PP DLocation where
    pp (PlainLocation pos t) = text $ tokenString t
    pp (ArrayLocation pos t e) = (text $ tokenString t)
                                 <> brackets (pp e)

block :: DParser Statement
block = Block <$> getPosition
        <* dopenbr
        <*> many varDecl
        <*> many statement
        <* dclosebr


data VarDecl = VarDecl SourcePos DType [Token]

instance PP VarDecl where
    pp (VarDecl pos t vars)
        = text "var" <+> pp t
          <+> (nest 3 $ vcat [text $ tokenString v | v <- vars])
          <+> (pp pos)

varDecl :: DParser VarDecl
varDecl = VarDecl <$> getPosition
          <*> dtype
          <*> sepBy1 ident dcomma
          <* dsemi


data DType = DInt
           | DBool
             deriving Show

instance PP DType where
    pp DInt = text "int"
    pp DBool = text "bool"

dtype :: DParser DType
dtype = ((DInt <$ dkeyword "int")
         <|> (DBool <$ dkeyword "boolean")) <?> "type"

statement :: DParser Statement
statement = ifSt
            <|> forSt
            <|> whileSt
            <|> returnSt
            <|> breakSt
            <|> continueSt
            <|> block
            <|> mcall
            <|> assign
            <?> "statement"
    where assign :: DParser Statement
          assign = AssignSt <$> getPosition
                   <*> location
                   <*> assignOp
                   <*> expr
                   <* dsemi
          mcall :: DParser Statement
          mcall = ExprSt
                  <$> (ExprMethod <$> getPosition <*> methodCall)
                  <* dsemi
          ifSt :: DParser Statement
          ifSt = IfSt <$> getPosition
                 <* dkeyword "if"
                 <*> between dopenp dclosep expr
                 <*> block
                 <*> (optionMaybe $ do
                        dkeyword "else"
                        block)
          forSt :: DParser Statement
          forSt = ForSt <$> getPosition
                  <* (dkeyword "for" >> dopenp)
                  <*> ident
                  <* dkeyword "="
                  <*> expr
                  <* dkeyword ";"
                  <*> expr
                  <* dclosep
                  <*> block
          whileSt :: DParser Statement
          whileSt = WhileSt <$> getPosition
                    <* dkeyword "while"
                    <*> between dopenp dclosep expr
                    <*> block
          returnSt :: DParser Statement
          returnSt = ReturnSt <$> getPosition
                     <* dkeyword "return"
                     <*> optionMaybe expr
                     <* dsemi
          breakSt :: DParser Statement
          breakSt = BreakSt <$> getPosition
                    <* dkeyword "break"
                    <* dsemi
          continueSt :: DParser Statement
          continueSt = ContinueSt <$> getPosition
                       <* dkeyword "continue"
                       <* dsemi

data AssignOp = Assign | IncAssign | DecAssign

instance Show AssignOp where
    show Assign = "="
    show IncAssign = "+="
    show DecAssign = "-="

assignOp :: DParser AssignOp
assignOp = (Assign <$ dkeyword "=")
           <|> (IncAssign <$ dkeyword "+=")
           <|> (DecAssign <$ dkeyword "-=")
           <?> "assignment operator"

data MethodCall = NormalMethod SourcePos Token [Expr]
                | CalloutMethod SourcePos Token [CalloutArg]

instance PP MethodCall where
    pp (NormalMethod pos t exps)
       = (text $ tokenString t)
         <> parens (hsep (punctuate (text ",") $ map pp exps))
    pp (CalloutMethod pos t exps)
       = (text "callout")
         <> parens (hsep (punctuate (text ",") $
                    [text $ tokenString t] ++ (map pp exps)))

data CalloutArg = CArgExpr Expr
                | CArgString Token

instance PP CalloutArg where
    pp (CArgExpr e) = pp e
    pp (CArgString t) = text $ show $ tokenString t

methodCall :: DParser MethodCall
methodCall = ((tLookAhead $ ident >> dopenp) >> normalMethod) -- lookahead two
             <|> calloutMethod
    where normalMethod :: DParser MethodCall
          normalMethod = NormalMethod <$> getPosition
                         <*> ident
                         <*> (between dopenp dclosep $ sepBy expr dcomma)
          calloutMethod :: DParser MethodCall
          calloutMethod = CalloutMethod <$> getPosition
                          <* dkeyword "callout"
                          <* dopenp
                          <*> dtoken StringLiteral
                          <*> many (dcomma *> calloutArg)
                          <* dclosep
          calloutArg :: DParser CalloutArg
          calloutArg = (CArgString <$> (dtoken StringLiteral))
                       <|> (CArgExpr <$> expr)

location :: DParser DLocation
location = do pos <- getPosition
              id <- ident
              index <- optionMaybe $ between dopensb dclosesb expr
              return $ case index of
                         Nothing -> PlainLocation pos id
                         Just i -> ArrayLocation pos id i

-- Precedence
-- 8. -
-- 7. !
-- 6. * / %
-- 5. + -
-- 4. < <= >= >
-- 3. == !=
-- 2. &&
-- 1. ||

data Expr = BinaryOp SourcePos Expr Token Expr
          | UnaryOp SourcePos Token Expr
          | ExprLiteral SourcePos Token
          | LoadLoc SourcePos DLocation
          | ExprMethod SourcePos MethodCall

class ASTNodePos a where
    getNodePos :: a -> SourcePos

instance ASTNodePos Expr where
    getNodePos (BinaryOp pos _ _ _) = pos
    getNodePos (UnaryOp pos _ _) = pos
    getNodePos (ExprLiteral pos _) = pos
    getNodePos (LoadLoc pos _) = pos
    getNodePos (ExprMethod pos _) = pos

instance PP Expr where
    pp (BinaryOp pos e t e2)
        = parens $ pp e <+> (text $ tokenString t) <+> pp e2
    pp (UnaryOp pos t e)
        = (text $ tokenString t) <> (pp e)
    pp (ExprLiteral pos t)
       = text $ tokenString t
    pp (LoadLoc pos loc) = pp loc
    pp (ExprMethod pos mc) = pp mc

makeBinOp :: (DParser Token) -> (DParser Expr) -> (DParser Expr)
makeBinOp op next = do pos <- getPosition
                       expr1 <- next
                       expr2s <- many (liftA2 (,) (op <?> "operator") next)
                       return $ makeBinOp' expr1 expr2s

    where makeBinOp' :: Expr -> [(Token, Expr)] -> Expr
          makeBinOp' expr1 [] = expr1
          makeBinOp' expr1 ((t, expr2):rest)
              = makeBinOp' (BinaryOp (getNodePos expr1) expr1 t expr2) rest

makeUnaryOp :: (DParser Token) -> (DParser Expr) -> (DParser Expr)
makeUnaryOp op next = do pos <- getPosition
                         mop <- optionMaybe (op <?> "unary operator")
                         expr <- next
                         return $ case mop of
                                    Nothing -> expr
                                    Just o -> UnaryOp pos o expr

expr :: DParser Expr
expr = exprBinOp1
    where exprBinOp1 = makeBinOp (dkeyword "||") exprBinOp2
          exprBinOp2 = makeBinOp (dkeyword "&&") exprBinOp3
          exprBinOp3 = makeBinOp (dkeywords ["==", "!="]) exprBinOp4
          exprBinOp4 = makeBinOp (dkeywords ["<", "<=", ">=", ">"]) exprBinOp5
          exprBinOp5 = makeBinOp (dkeywords ["+", "-"]) exprBinOp6
          exprBinOp6 = makeBinOp (dkeywords ["*", "/", "%"]) unaryOp7
          unaryOp7 = makeUnaryOp (dkeyword "!") unaryOp8
          unaryOp8 = makeUnaryOp (dkeyword "-") nullary9
          nullary9 :: DParser Expr
          nullary9 = (ExprMethod <$> getPosition <*> methodCall)
                     <|> (LoadLoc <$> getPosition <*> location)
                     <|> literal
                     <|> between dopenp dclosep expr

literal :: DParser Expr
literal = ExprLiteral <$> getPosition
          <*> (dtoken IntLiteral <|> dtoken CharLiteral <|> dtoken BooleanLiteral)

ident = dtoken Identifier
