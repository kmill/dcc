module Scanner ( TokenType(..), Token(..), runScanner ) where

import Text.ParserCombinators.Parsec hiding (alphaNum)
import Text.ParserCombinators.Parsec.Char hiding (alphaNum)
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Prim
import Text.Printf
import Control.Monad
import Control.Applicative (Applicative, pure, (<$>), (<*>), (<*), (*>))
import Data.Char (ord)
import Data.List (concatMap)

import CLI
import Data.Maybe (fromMaybe)

reservedWords = ["boolean", "break", "callout", "class", "continue"
                ,"else", "for", "if", "int", "return", "void", "while"]
-- The symbols list is ordered so prefixes don't appear first.
symbols = ["{", "}", "(", ")", "[", "]", ";", ",",
           "==", "=", "+=", "-=", "+", "-", "*", "/", "%",
           "<=", ">=", "<", ">", "!=", "!", "&&", "||"]

data TokenType = CharLiteral
               | IntLiteral
               | BooleanLiteral
               | StringLiteral
               | Identifier
               | Keyword
                 deriving (Eq)

data Token = Token { tokenType :: TokenType
                   , tokenString :: String
                   , tokenPos :: SourcePos }
           -- TokenError takes an unexpected char and maybe the
           -- expected char; used for 6.035 compatibility mode.
           | TokenError SourcePos (Maybe Char) (Maybe Char)

instance Show Token where
    show t@(Token {tokenString=s})
        = case tokenType t of
            CharLiteral -> printf "character '%s'" $ escStr s
            IntLiteral -> printf "literal %s" s
            BooleanLiteral -> printf "boolean %s" s
            StringLiteral -> printf "string \"%s\"" $ escStr s
            Identifier -> printf "identifier \"%s\"" s
            Keyword -> printf "keyword \"%s\"" s
        where
          escChar :: Char -> String
          escChar x
              = case x of
                  '\\' -> "\\\\"
                  '\t' -> "\\t"
                  '\n' -> "\\n"
                  '"'  -> "\\\""
                  '\'' -> "\\'"
                  x    -> [x]
          escStr :: String -> String
          escStr = concatMap escChar

instance Show TokenType where
    show CharLiteral = "character literal"
    show IntLiteral = "integer literal"
    show BooleanLiteral = "boolean literal"
    show StringLiteral = "string literal"
    show Identifier = "identifier"
    show Keyword = "keyword"


type Scanner a = GenParser Char ScannerState a
data ScannerState = ScannerState { scanner6035CompatMode :: Bool }


-- Makes a parser which returns a Token whose content is the output of
-- the given parser.
makeToken :: TokenType -> Scanner String -> Scanner Token
makeToken restype parser =
    do pos <- getPosition
       text <- parser
       return $ Token restype text pos

-- Takes maybe an expected character and creates a TokenError using
-- the current position.  This Scanner eats a character.
makeTokenError :: Maybe Char -> Scanner Token
makeTokenError mc = do pos <- getPosition
                       c <- optionMaybe anyChar
                       -- dumb hack to satisfy 6.035 compatibility...
                       let hack = case c of
                                    Just '\t' -> 7
                                    Just '\n' -> 1
                                    _ -> 1
                       setPosition (incSourceColumn pos hack)
                       return $ TokenError pos c mc

-- Takes maybe an expected character, checks if we're in 6.035
-- compatibility mode, and then, if so, calls makeTokenError.
scanError :: Maybe Char -> Scanner Token
scanError mc = do s <- getState
                  case scanner6035CompatMode s of
                    False -> mzero
                    True -> makeTokenError mc

-- ErrorScanner is a Scanner that contains an Either.  The bind
-- operation short circuits when the contained Either is a Left, and
-- is a normal Scanner when it's a Right.
newtype ErrorScanner a = ErrorScanner { runErrorScanner :: Scanner (Either Token a) }

instance Monad (Either a) where
    return = Right
    (Right x) >>= f  = f x
    (Left x) >>= _   = Left x
instance Applicative (Either a) where
    pure = Right
    a <*> b = do x <- a
                 y <- b
                 return $ x y

instance Monad ErrorScanner where
    return   = ErrorScanner . return . return
    m >>= f  = ErrorScanner $ do
                 ea <- runErrorScanner m
                 case ea of
                   Left l -> return $ Left l
                   Right r -> runErrorScanner $ f r
    fail _   = ErrorScanner $ (Left <$> scanError Nothing)

instance Functor ErrorScanner where
    fmap f = ErrorScanner . fmap (fmap f) . runErrorScanner

liftS :: Scanner a -> ErrorScanner a
liftS m = ErrorScanner $ Right <$> m

-- Takes maybe the expected character and returns an ErrorScanner
-- which fails by returning a Left TokenError, thus short-circuiting
-- the rest of the ErrorScanner.
scanFail :: Maybe Char -> ErrorScanner a
scanFail mc = ErrorScanner $ Left <$> scanError mc

-- Takes an ErrorScanner and pulls out whatever was in the Left or
-- Right, thus bringing it back to a Scanner.
catchErrorScanner :: ErrorScanner Token -> Scanner Token
catchErrorScanner ms
    = do res <- runErrorScanner ms
         case res of
           Left l -> return l
           Right r -> return r

-- This is the same as <?> for Scanners but instead for an
-- ErrorScanner
(<<?>>) :: ErrorScanner a -> String -> ErrorScanner a
p <<?>> s = ErrorScanner $ (runErrorScanner p <?> s)


-- This is the same as <|> but for ErrorScanner instead of Scanner.
-- Importantly, if the left operand returns a Left, then that is the
-- same as succeeding, so the right operand is not run.
(<<|>>) :: ErrorScanner a -> ErrorScanner a -> ErrorScanner a
p1 <<|>> p2 = ErrorScanner $ runErrorScanner p1 <|> runErrorScanner p2

infix 0 <<?>>
infixr 1 <<|>>

---
--- Actual scanners
---

-- Matches a hex/bin/dec literal.
intLiteral :: Scanner Token
intLiteral = catchErrorScanner $ hexLiteral <<|>> binLiteral <<|>> decLiteral
    where
      intLiteral' :: String -> Scanner Char -> ErrorScanner Token
      intLiteral' prefix digitParser =
          do pos <- liftS getPosition
             liftS $ try (string prefix)
             digit1 <- (liftS digitParser) <<|>> scanFail Nothing
             digits <- liftS $ many digitParser
             return $ Token IntLiteral (prefix ++ (digit1:digits)) pos

      hexLiteral = intLiteral' "0x" hexDigit
      binLiteral = intLiteral' "0b" $ oneOf "01"
      decLiteral = liftS $ makeToken IntLiteral $ many1 digit

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
reserved s = try (string s <* notFollowedBy alphaNum)

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


-- This matches any of the symbol tokens like parens, braces,
-- operators, etc.  They come from the symbols variable.
symbolTokens :: Scanner Token
symbolTokens = choice [makeToken Keyword (try $ string s) | s <- symbols]

-- Represents a character which can appear in a string
dchar :: ErrorScanner Char
dchar = do (liftS $ char '\\') <<?>> "backslash"
           escapedChar <<|>> scanFail Nothing -- scanFail since ate backslash
        <<|>> ((liftS $ satisfy isValidChar) <<?>> "valid non-quote character")
    where
      escapedTable = [('\'', '\''), ('"', '"'), ('\\', '\\'), ('t', '\t'), ('n', '\n')]
      escapedChar :: ErrorScanner Char
      escapedChar = foldr1 (<<|>>) [(liftS $ char c) >> return r | (c,r) <- escapedTable]
      isValidChar c = (ord c) >= 32 && (ord c) <= 126 && not (c `elem` "'\"")


-- mchar is a lifted char function but with a built-in scanFail
mchar :: Char -> ErrorScanner Char
mchar c = (liftS $ char c) <<|>> scanFail (Just c)

-- Takes a character which should surround the parser.  This parser
-- fails if the first character is not matched, and uses mchar to
-- scanFail if the last character is not matched.  It returns the
-- result of the parser along with the position of the opening
-- character.  Make sure the passed in parser handles its own errors!
mbetween :: Char -> ErrorScanner a -> ErrorScanner (a, SourcePos)
mbetween c p = do pos <- liftS getPosition
                  liftS $ char c
                  minside <- p
                  mchar c
                  return (minside, pos)

-- Like optionMaybe, but lifted to ErrorScanner.
mOptionMaybe :: ErrorScanner a -> ErrorScanner (Maybe a)
mOptionMaybe p = (liftM Just p) <<|>> return Nothing

-- Like many, but lifted to ErrorScanner.
mmany :: ErrorScanner a -> ErrorScanner [a]
mmany p = do mx <- mOptionMaybe p
             case mx of
               Nothing -> return []
               Just x -> fmap (x:) (mmany p)

charLiteral :: Scanner Token
charLiteral = catchErrorScanner $ do
                (c, pos) <- mbetween '\'' (dchar <<|>> scanFail Nothing)
                return $ Token CharLiteral [c] pos

stringLiteral :: Scanner Token
stringLiteral = catchErrorScanner $ do
                  (s, pos) <- mbetween '"' (mmany dchar)
                  return $ Token StringLiteral s pos

-- This is the main token scanner!
dctoken :: Scanner Token
dctoken = keywords <|> boolLiteral <|> identifier <|> intLiteral
          <|> charLiteral <|> stringLiteral <|> symbolTokens
          <|> (scanError Nothing) -- to handle 6.035 compatibility mode


scanner :: Scanner [Token]
scanner = do whitespace
             manyTill token' eof
    where token' = do tok <- dctoken
                      whitespace
                      return tok

runScanner :: CompilerOpts -> String -> String -> Either ParseError [Token]
runScanner opts ifname input
    = runParser scanner scanState ifname input
      where scanState = ScannerState { scanner6035CompatMode=compatMode opts }
