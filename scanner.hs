import IO hiding (try)
import Text.ParserCombinators.Parsec hiding (alphaNum)
import Text.ParserCombinators.Parsec.Char hiding (alphaNum)
import Control.Monad
import Data.Char (ord)
import System.Environment
import Data.List (concatMap)

-- Just a lifted version of (++).
(<++>) :: Scanner [a] -> Scanner [a] -> Scanner [a]
(<++>) = liftM2 (++)

reservedWords = ["boolean", "break", "callout", "class", "continue"
                ,"else", "for", "if", "int", "return", "void", "while"]
otherTokens = ["{", "}", "(", ")", "[", "]", ";", ",",
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

instance Show Token where
    show x = ln ++ tokType ++ " " ++ tokStr
        where ln = show $ sourceLine $ tokenPos x
              tokType = case tokenType x of
                          Keyword -> ""
                          t -> " " ++ (show t)
              tokStr = case tokenType x of
                         CharLiteral -> "'" ++ escaped ++ "'"
                         StringLiteral -> "\"" ++ escaped ++ "\""
                         _ -> tokenString x
                  where escaped = dcEscapeStr $ tokenString x

dcEscapeChar '\\' = "\\\\"
dcEscapeChar '\t' = "\\t"
dcEscapeChar '\n' = "\\n"
dcEscapeChar '"' = "\\\""
dcEscapeChar '\'' = "\\'"
dcEscapeChar x = [x]

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
    where identifier' = (liftM2 (:)) alpha (many alphaNum)  <?> "identifier"

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
symbolTokens = choice $ map (\s -> makeToken Keyword (try $ string s)) otherTokens

dchar :: Scanner Char
dchar = ((char '\\') >> escapedChar)
        <|> ((satisfy isValidChar) <?> "valid non-quote character")
    where
      escapedTable = [('\'', '\''), ('"', '"'), ('\\', '\\'), ('t', '\t'), ('n', '\n')]
      escapedChar :: Scanner Char
      escapedChar = choice $ map (\(c,r) -> (char c) >> (return r)) escapedTable

      isValidChar c = (ord c) >= 32 && (ord c) <= 126 && not (c `elem` "'\"")

charLiteral :: Scanner Token
charLiteral = makeToken CharLiteral clscanner
    where clscanner = do c <- between (char '\'') (char '\'') dchar
                         return $ [c]

stringLiteral :: Scanner Token
stringLiteral = makeToken StringLiteral $ (between (char '"') (char '"') $ many dchar)

parsecPlus :: GenParser tok st a -> GenParser tok st a -> GenParser tok st a
parsecPlus (Parser p1) (Parser p2)
    = Parser (\state ->
        case (p1 state) of        
          Empty (Error err) -> case (p2 state) of
                                 Empty reply -> Empty (mergeErrorReply err reply)
                                 consumed    -> consumed
          other             -> other
      )

data ScannerErrors = ScannerErrors [

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
