import IO hiding (try)
import Text.ParserCombinators.Parsec hiding (alphaNum)
import Text.ParserCombinators.Parsec.Char hiding (alphaNum)
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Prim
import Control.Monad
import Control.Applicative (pure, (<*>))
import Data.Char (ord)
import System.Environment
import Data.List (concatMap)

-- Just a lifted version of (++).
(<++>) :: Scanner [a] -> Scanner [a] -> Scanner [a]
(<++>) = liftM2 (++)

reservedWords = ["boolean", "break", "callout", "class", "continue"
                ,"else", "for", "if", "int", "return", "void", "while"]
symbols = ["{", "}", "(", ")", "[", "]", ";", ",",
           "=", "+=", "-=", "+", "-", "*", "/", "%",
           "<=", ">=", "<", ">", "==", "!=", "!", "&&", "||"]

data TokenType = CharLiteral
               | IntLiteral
               | BooleanLiteral
               | StringLiteral
               | Identifier
               | Keyword

data Token = Token { tokenType :: TokenType
                   , tokenString :: String
                   , tokenPos :: SourcePos }
           | TokenError SourcePos Char

instance Show Token where
    show (TokenError err) = show err
    show x = ln ++ tokType ++ " " ++ tokStr
        where ln = show $ sourceLine $ tokenPos x
              -- gives a textual representation of the type field
              tokType = case tokenType x of
                          Keyword -> ""
                          t -> " " ++ (show t)
              -- gives a textual representation of the string data,
              -- escaping as necessary
              tokStr = case tokenType x of
                         CharLiteral -> "'" ++ escaped ++ "'"
                         StringLiteral -> "\"" ++ escaped ++ "\""
                         _ -> tokenString x
                  where escaped = dcEscapeStr $ tokenString x

dcEscapeChar :: Char -> String
dcEscapeChar '\\' = "\\\\"
dcEscapeChar '\t' = "\\t"
dcEscapeChar '\n' = "\\n"
dcEscapeChar '"' = "\\\""
dcEscapeChar '\'' = "\\'"
dcEscapeChar x = [x]

dcEscapeStr :: String -> String
dcEscapeStr = concatMap dcEscapeChar

instance Show TokenType where
    show CharLiteral = "CHARLITERAL"
    show IntLiteral = "INTLITERAL"
    show BooleanLiteral = "BOOLEANLITERAL"
    show StringLiteral = "STRINGLITERAL"
    show Identifier = "IDENTIFIER"
    show Keyword = "KEYWORD"

type Scanner a = GenParser Char () a

-- Makes a parser which returns a Token whose content is the output of
-- the given parser.
makeToken :: TokenType -> Scanner String -> Scanner Token
makeToken restype parser =
    do pos <- getPosition
       text <- parser
       return $ Token restype text pos

intLiteral :: Scanner Token
intLiteral = hexLiteral <|> binLiteral <|> decLiteral
    where
      intLiteral' :: String -> Scanner Char -> Scanner Token
      intLiteral' prefix digitParser =
          makeToken IntLiteral $ (try (string prefix)) <++> (many1 digitParser)
      
      hexLiteral = intLiteral' "0x" hexDigit
      binLiteral = intLiteral' "0b" $ oneOf "01"
      decLiteral = intLiteral' "" digit

-- alpha is [a-zA-Z_]
alpha :: Scanner Char
alpha = letter <|> (char '_')     <?> "alpha"
alphaNum :: Scanner Char
alphaNum = alpha <|> digit        <?> "alphanumeric"

identifier :: Scanner Token
identifier = makeToken Identifier identifier'
    where identifier' = liftM2 (:) alpha (many alphaNum)  <?> "identifier"

-- Parses a particular string as long as it's not followed by alphaNum
reserved :: String -> Scanner String
reserved s = do try (string s >> notFollowedBy alphaNum)
                return s

boolLiteral :: Scanner Token
boolLiteral = (boolReserved "true") <|> (boolReserved "false")  <?> "boolean"
    where boolReserved s = makeToken BooleanLiteral (reserved s)

eol = eof <|> ((char '\n') >> return ())  <?> "end of line"

comment = do try $ string "//"
             manyTill anyChar eol
             return ()

whitespace = do many $ ((oneOf " \n\t") >> return ()) <|> comment
                return ()

keyword :: String -> Scanner Token
keyword s = makeToken Keyword $ reserved s

keywordSymbol :: String -> Scanner Token
keywordSymbol s = makeToken Keyword (string s)

keywords :: Scanner Token
keywords = choice $ map keyword reservedWords

symbolTokens :: Scanner Token
symbolTokens = choice $ map (\s -> makeToken Keyword (try $ string s)) symbols

dchar :: Scanner Char
dchar = (((char '\\') <?> "backslash" )>> escapedChar)
        <|> ((satisfy isValidChar) <?> "valid non-quote character")
    where
      escapedTable = [('\'', '\''), ('"', '"'), ('\\', '\\'), ('t', '\t'), ('n', '\n')]
      escapedChar :: Scanner Char
      escapedChar = choice $ map (\(c,r) -> (char c) >> (return r)) escapedTable

      isValidChar c = (ord c) >= 32 && (ord c) <= 126 && not (c `elem` "'\"")

charLiteral :: Scanner Token
charLiteral = makeToken CharLiteral clscanner
    where clscanner = do c <- between squote squote dchar
                         return $ [c]
          squote = (char '\'') <?> "single quote"

stringLiteral :: Scanner Token
stringLiteral = makeToken StringLiteral $ (between dquote dquote $ many dchar)
    where dquote = (char '"') <?> "double quote"

scanOne :: Scanner Token
scanOne = do st <- getState
             toks <- lift stateInput getParserState
             pos <- getPosition
             case runParser st (sourceName pos) toks of
               Right x -> return x
               Left err -> do eatUntil $ errorPos TokenError err

makeError :: Scanner Token
makeError = do c <- anyChar
               

scanner :: Scanner [Token]
scanner = do whitespace
             scanner'
    where scanner' :: Scanner [Token]
          scanner' = (eof >> return []) <|>
                     do tok <- token
                        whitespace
                        rest <- scanner'
                        return $ tok:rest
          token :: Scanner Token
          token = keywords <|> boolLiteral <|> identifier <|> intLiteral
                  <|> charLiteral <|> stringLiteral <|> symbolTokens

scanFile fname = do input <- readFile fname
--                    let input = "'\\p'"
                    let res = runParser scanner () fname input
                    case res of
                      Left err -> print err
                      Right v -> printScannerResult v

main :: IO ()
main = do args <- getArgs
          let fname = args !! (length args - 1)
          scanFile $ fname

printScannerResult :: [Token] -> IO ()
printScannerResult (t:ts) = do putStrLn $ show t
                               printScannerResult ts
printScannerResult [] = return ()
