module Parser(runDParser) where

import Scanner
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import CLI
import Control.Applicative (Applicative, pure, (<$>), (<*>), (<*), (*>), (<$))

import Text.PrettyPrint.HughesPJ

-- at this stage, all parsers must return ()
type DParser a = GenParser Token DParserState a
data DParserState = DParserState

runDParser :: CompilerOpts -> [Token] -> Either ParseError DProgram
runDParser opts input
    = runParser dprogram parseState "" input
      where parseState = DParserState

dtoken :: TokenType -> DParser Token
dtoken tt = dtoken' (\t -> tt == tokenType t) <?> (show tt)

dtoken' :: (Token -> Bool) -> DParser Token
dtoken' p = token showtok tokenPos testtok
    where showtok = show
          testtok t = if p t then Just t else Nothing

dkeyword :: String -> DParser Token
dkeyword s = token showtok tokenPos testtok <?> "\"" ++ s ++ "\""
    where showtok = show
          testtok t = if tokenType t == Keyword && tokenString t == s
                      then Just t else Nothing

--dkeywords :: [String] -> a
dkeywords = (foldl1 (<|>)) . (map dkeyword)

class PP a where
    pp :: a -> Doc

data DProgram = DProgram SourcePos [FieldDecl] [MethodDecl]

instance Show DProgram where
    show = render . pp

instance PP DProgram where
    pp (DProgram pos fields methods)
        = text "Program"
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

data FieldVar = PlainVar Token
              | ArrayVar Token Token
                deriving Show

instance PP FieldVar where
    pp (PlainVar t) = text $ tokenString t
    pp (ArrayVar t l) = (text $ tokenString t) <> brackets (text $ show l)

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

data MethodDecl = MethodDecl SourcePos MethodType Token [MethodArg]

instance PP MethodDecl where
    pp (MethodDecl pos t tok args)
        = text "methoddecl" <+> (pp t) <+> (text $ tokenString tok)
          <> parens (hsep $ punctuate comma [pp a | a <- args])


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
             <*> (between dopenp dclosep $ sepBy arg dcomma)
             <* block
    where arg = MethodArg
                <$> dtype
                <*> ident

data Statement = Block SourcePos [VarDecl] [Statement]
               | IfSt SourcePos Expr Statement (Maybe Statement)
               | WhileSt SourcePos Expr Statement
               | ReturnSt SourcePos (Maybe Expr)
               | BreakSt SourcePos
               | CountinueSt SourcePos
               | ExprSt Expr
               | AssignSt

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
statement = do (ifSt
                <|> forSt
                <|> whileSt
                <|> returnSt
                <|> breakSt
                <|> continueSt
                <|> block
                <|> (methodCall >> dsemi)
                <|> assign) <?> "statement"
               return ()
    where assign = do location
                      assignOp
                      expr
                      dsemi
                      return ()
          ifSt = do dkeyword "if"
                    between dopenp dclosep expr
                    block
                    optionMaybe $ do
                      dkeyword "else"
                      block
                    return ()
          forSt = do dkeyword "for"
                     between dopenp dclosep $ do
                       ident
                       dkeyword "="
                       expr
                       dkeyword ";"
                       expr
                     block
                     return ()
          whileSt = do dkeyword "while"
                       between dopenp dclosep expr
                       block
                       return ()
          returnSt = do dkeyword "return"
                        optionMaybe expr
                        dsemi
                        return ()
          breakSt = do dkeyword "break"
                       dsemi
                       return ()
          continueSt = do dkeyword "continue"
                          dsemi
                          return ()

assignOp :: DParser ()
assignOp = do dkeyword "=" <|> dkeyword "+=" <|> dkeyword "-="
              return ()

methodCall :: DParser ()
methodCall = ((tLookAhead $ ident >> dopenp) >> normalMethod)
             <|> calloutMethod
    where normalMethod = do ident
                            between dopenp dclosep $ sepBy expr dcomma
                            return ()
          calloutMethod = do dkeyword "callout"
                             between dopenp dclosep $ do
                               dtoken StringLiteral
                               many $ do
                                 dcomma
                                 calloutArg
                             return ()
          calloutArg = do expr <|> (() <$ dtoken StringLiteral)
                          return ()

location :: DParser ()
location = do ident
              optionMaybe $ between dopensb dclosesb expr
              return ()

-- Precedence
-- 8. -
-- 7. !
-- 6. * / %
-- 5. + -
-- 4. < <= >= >
-- 3. == !=
-- 2. &&
-- 1. ||

makeBinOp op next = do next
                       many ((op <?> "operator") >> next)
                       return ()

makeUnaryOp op next = do optionMaybe (op <?> "unary operator")
                         next
                         return ()

expr :: DParser ()
expr = exprBinOp1
    where exprBinOp1 = makeBinOp (dkeyword "||") exprBinOp2
          exprBinOp2 = makeBinOp (dkeyword "&&") exprBinOp3
          exprBinOp3 = makeBinOp (dkeywords ["==", "!="]) exprBinOp4
          exprBinOp4 = makeBinOp (dkeywords ["<", "<=", ">=", ">"]) exprBinOp5
          exprBinOp5 = makeBinOp (dkeywords ["+", "-"]) exprBinOp6
          exprBinOp6 = makeBinOp (dkeywords ["*", "/", "%"]) unaryOp7
          unaryOp7 = makeUnaryOp (dkeyword "!") unaryOp8
          unaryOp8 = makeUnaryOp (dkeyword "-") nullary9
          nullary9 = methodCall
                     <|> location
                     <|> literal
                     <|> between dopenp dclosep expr

literal :: DParser ()
literal = do dtoken IntLiteral <|> dtoken CharLiteral <|> dtoken BooleanLiteral
             return ()

ident = dtoken Identifier
