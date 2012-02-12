module Scanner ( TokenType(..), Token(..), runScanner ) where

import Text.ParserCombinators.Parsec hiding (alphaNum)
import Text.ParserCombinators.Parsec.Char hiding (alphaNum)
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Prim
import Text.Printf
import Control.Monad
import Control.Applicative (pure, (<*>))
import Data.Char (ord)
import Data.List (concatMap)

import CLI
import Data.Maybe (fromMaybe)

-- Just a lifted version of (++).
(<++>) :: Scanner [a] -> Scanner [a] -> Scanner [a]
(<++>) = liftM2 (++)

type Scanner a = GenParser Char ScannerState a
data ScannerState = ScannerState { scanner6035CompatMode :: Bool }

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

data Token = Token { tokenType :: TokenType
                   , tokenString :: String
                   , tokenPos :: SourcePos }
           -- TokenError takes an unexpected char and maybe the
           -- expected char; used for 6.035 compatibility mode.
           | TokenError SourcePos (Maybe Char) (Maybe Char)

-- Wraps the second string with two copies of the first string.
quotify :: String -> String -> String
quotify q s = q ++ s ++ q

instance Show Token where
    show (TokenError pos c mc)
        = compatPos
          ++ case mc of
               Just exc -> printf "expecting %s, found '%s'"
                           (compatChar mc) (fromMaybe "EOF" $ c >>= Just . escChar)
               Nothing -> "unexpected char: " ++ (compatChar c)
        where compatPos = printf "%s line %i:%i: "
                          (sourceName pos) (sourceLine pos) (sourceColumn pos)
              compatChar (Just c) = if 32 <= (ord c) && (ord c) <= 126
                                    then quotify "'" [c]
                                    else printf "0x%X" c
              compatChar Nothing = "EOF"

              -- Escapes a character for 6.035 compatibility... It
              -- requires no backslashes in a "found" string!!!
              escChar :: Char -> String
              escChar x
                  = case x of
                      '\\' -> "\\"
                      '\t' -> "\\t"
                      '\n' -> "\\n"
                      '"'  -> "\""
                      '\'' -> "'"
                      x    -> [x]
                                  
    show x = ln ++ tokType ++ " " ++ tokStr
        where ln = show $ sourceLine $ tokenPos x
              -- gives a textual representation of the type field
              tokType = case tokenType x of
                          Keyword -> ""
                          t -> " " ++ (show t)
              -- gives a textual representation of the string data,
              -- escaping as necessary
              tokStr = case tokenType x of
                         CharLiteral -> quotify "'" escaped
                         StringLiteral -> quotify "\"" escaped
                         _ -> tokenString x
              escaped = concatMap escChar $ tokenString x

              -- Escapes a character for 6.035 compatibility...
              escChar :: Char -> String
              escChar x
                  = case x of
                      '\\' -> "\\\\"
                      '\t' -> "\\t"
                      '\n' -> "\\n"
                      '"'  -> "\\\""
                      '\'' -> "\\'"
                      x    -> [x]

instance Show TokenType where
    show CharLiteral = "CHARLITERAL"
    show IntLiteral = "INTLITERAL"
    show BooleanLiteral = "BOOLEANLITERAL"
    show StringLiteral = "STRINGLITERAL"
    show Identifier = "IDENTIFIER"
    show Keyword = "KEYWORD"

-- Takes maybe an expected character and creates a TokenError using
-- the current position.  This Scanner eats a character.
makeTokenError :: Maybe Char -> Scanner Token
makeTokenError mc = do pos <- getPosition
                       c <- (liftM Just anyChar) <|> (eof >> return Nothing)
                       let hack = case c of  -- dumb hack to satisfy 6.035...
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

-- Checks if we're in 6.035 compatibility mode, and return Nothing if
-- we are, or does mzero otherwise.
scanNone :: Scanner (Maybe a)
scanNone = do s <- getState
              case scanner6035CompatMode s of
                False -> mzero
                True -> return $ Nothing

-- Makes a parser which returns a Token whose content is the output of
-- the given parser.
makeToken :: TokenType -> Scanner String -> Scanner Token
makeToken restype parser =
    do pos <- getPosition
       text <- parser
       return $ Token restype text pos


---
--- Actual scanners
---

-- Matches a hex/bin/dec literal.
intLiteral :: Scanner Token
intLiteral = hexLiteral <|> binLiteral <|> decLiteral
    where
      intLiteral' :: String -> Scanner Char -> Scanner Token
      intLiteral' prefix digitParser =
          do pos <- getPosition
             try (string prefix)
             mdigit <- (liftM Just digitParser) <|> scanNone
             case mdigit of
               Just digit -> do digits <- many digitParser
                                return $ Token IntLiteral (prefix ++ (digit:digits)) pos
               Nothing -> scanError Nothing
      
      hexLiteral = intLiteral' "0x" hexDigit
      binLiteral = intLiteral' "0b" $ oneOf "01"
      decLiteral = makeToken IntLiteral $ many1 digit

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

dchar :: Scanner (Maybe Char)
dchar = (((char '\\') <?> "backslash") >> (escapedChar <|> scanNone)) -- scanNone since ate backslash
        <|> (((satisfy isValidChar)>>=(\c -> return $ Just c)) <?> "valid non-quote character")
--        <|> (eof >> scanNone)
    where
      escapedTable = [('\'', '\''), ('"', '"'), ('\\', '\\'), ('t', '\t'), ('n', '\n')]
      escapedChar :: Scanner (Maybe Char)
      escapedChar = choice $ map (\(c,r) -> (char c) >> (return $ Just r)) escapedTable

      isValidChar c = (ord c) >= 32 && (ord c) <= 126 && not (c `elem` "'\"")


-- mchar is char but with a built-in scanNone (so it uses Maybe to
-- signal whether the char worked)
mchar :: Char -> Scanner (Maybe Char)
mchar c = ((char c) >> (return $ Just c)) <|> scanNone

-- Takes a character that should surround a parser.  If either the
-- parser or the matching of the second iteration of the character
-- fail, then makeTokenError is called.
mbetween c p handle
    = do pos <- getPosition
         char c
         minside <- p
         case minside of
           Nothing -> makeTokenError Nothing
           Just inside ->
               do mc <- (mchar c) <|> scanNone
                  case mc of
                    Nothing -> makeTokenError (Just c)
                    Just _ -> return $ handle inside pos

-- Runs a parser as many times as it matches.  But, if the parser
-- returns Nothing (because of a scanNone, for instance), it is
-- treated as an error, and then this entire parser returns Nothing as
-- well.
mmany :: Scanner (Maybe a) -> Scanner (Maybe [a])
mmany s = do mas <- mmany' []
             case mas of
               Nothing -> return Nothing
               (Just as) -> return $ Just $ reverse as
    where mmany' cs = do emc <- (liftM Just s) <|> (return $ Nothing)
                         case emc of
                           Nothing -> return $ Just cs
                           (Just mc) ->
                               case mc of
                                 Nothing -> return Nothing
                                 (Just c) -> mmany' (c:cs)

charLiteral :: Scanner Token
charLiteral = mbetween '\'' (dchar <|> scanNone) (\c -> Token CharLiteral [c])

stringLiteral :: Scanner Token
stringLiteral = mbetween '"' (mmany dchar) (Token StringLiteral)

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
