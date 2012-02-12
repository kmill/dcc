module Parser() where

import Scanner
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error

type DParser a = GenParser Token DParserState a
data DParserState = DParserState

dtoken :: TokenType -> DParser Token
dtoken tt = token showtok tokenPos testtok
    where showtok = show
          testtok t = if tt == tokenType t then Just t else Nothing

dkeyword :: String -> DParser Token
dkeyword s = token showtok tokenPos testtok
    where showtok = show
          testtok t = if tokenType t == Keyword && tokenString t == s
                      then Just t else Nothing

dprogram = do dkeyword "class" >> dkeyword "{"
              fds <- many fieldDecl
              mds <- many methodDecl
              dkeyword "}"

fieldDecl = do try dtype
               sepBy1 (plainVar <|> arrayVar) (dkeyword ",")
               dkeyword ";"
    where plainVar = do try ident
                        return ()
          arrayVar = do try ident
                        dkeyword "["
                        dtoken IntLiteral
                        dkeyword "]"

methodDecl = do try (dtype <|> dkeyword "void")
                try ident
                dkeyword "("
                sepBy1 arg (dkeyword ",")
                dkeyword ")"
                block
    where arg = do dtype
                   ident

block = do dkeyword "{"
           many varDecl
           many statement
           dkeyword "}"

varDecl = do try dtype
             sepBy1 ident (dkeyword ",")
             dkeyword ";"

statement = assign <|> methodCall
            <|> ifSt
            <|> forSt
            <|> whileSt
            <|> returnSt
            <|> breakSt
            <|> continueSt
            <|> block
    where assign = do try location
                      assignOp
                      expr
                      return ()
          methodCall

dtype = dkeyword "int" <|> dkeyword "boolean"

ident = dtoken Identifier
