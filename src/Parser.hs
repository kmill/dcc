module Parser(runDParser) where

import Scanner
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import CLI

-- at this stage, all parsers must return ()
type DParser = GenParser Token DParserState ()
data DParserState = DParserState

runDParser :: CompilerOpts -> [Token] -> Either ParseError ()
runDParser opts input
    = runParser dprogram parseState "" input
      where parseState = DParserState

dtoken :: TokenType -> DParser
dtoken tt = (token showtok tokenPos testtok <?> (show tt)) >> return ()
    where showtok = show
          testtok t = if tt == tokenType t then Just t else Nothing

dkeyword :: String -> DParser
dkeyword s = (token showtok tokenPos testtok <?> "\"" ++ s ++ "\"") >> return ()
    where showtok = show
          testtok t = if tokenType t == Keyword && tokenString t == s
                      then Just t else Nothing

--dkeywords :: [String] -> a
dkeywords = (foldl1 (<|>)) . (map dkeyword)

-- dprogram is the main entry point into the parser
dprogram :: DParser
dprogram = do dkeyword "class" 
              ident
              dkeyword "{"
              many fieldDecl
              many methodDecl
              dkeyword "}"
              return ()

dsemi :: DParser
dsemi = dkeyword ";" >> return ()

dopenp :: DParser
dopenp = dkeyword "(" >> return ()
dclosep :: DParser
dclosep = dkeyword ")" >> return ()
dopensb :: DParser
dopensb = dkeyword "[" >> return ()
dclosesb :: DParser
dclosesb = dkeyword "]" >> return ()
dopenbr :: DParser
dopenbr = dkeyword "{" >> return ()
dclosebr :: DParser
dclosebr = dkeyword "}" >> return ()


tLookAhead = try . lookAhead

fieldDecl :: DParser
fieldDecl = do try $ do
                 dtype
                 tLookAhead $ ident >> (dsemi <|> dopensb <|> dkeyword ",")
               sepBy1 (arrayVar <|> plainVar) (dkeyword ",")
               dsemi
               return ()
    where plainVar = do try ident
                        return ()
          arrayVar = do try $ do
                          ident
                          dopensb
                        dtoken IntLiteral
                        dclosesb
                        return ()

methodDecl :: DParser
methodDecl = do try (dtype <|> dkeyword "void")
                ident
                between dopenp dclosep $ sepBy arg (dkeyword ",")
                block
                return ()
    where arg = do dtype
                   ident
                   return ()

block :: DParser
block = do between dopenbr dclosebr $ do
             many varDecl
             many statement
             return ()

varDecl :: DParser
varDecl = do dtype
             sepBy1 ident (dkeyword ",")
             dsemi
             return ()

dtype :: DParser
dtype = (dkeyword "int" <|> dkeyword "boolean") <?> "type"

statement :: DParser
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

assignOp :: DParser
assignOp = do dkeyword "=" <|> dkeyword "+=" <|> dkeyword "-="
              return ()

methodCall :: DParser
methodCall = ((tLookAhead $ ident >> dopenp) >> normalMethod)
             <|> calloutMethod
    where normalMethod = do ident
                            between dopenp dclosep $ sepBy expr (dkeyword ",")
                            return ()
          calloutMethod = do dkeyword "callout"
                             between dopenp dclosep $ do
                               dtoken StringLiteral
                               many $ do
                                 dkeyword ","
                                 calloutArg
                             return ()
          calloutArg = do expr <|> dtoken StringLiteral

location :: DParser
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

expr :: DParser
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

literal :: DParser
literal = dtoken IntLiteral <|> dtoken CharLiteral <|> dtoken BooleanLiteral

ident = dtoken Identifier
