-- | This module implements a scanner for the Decaf language for
-- 6.035.  It uses the 'Text.ParserCombinators.Parsec' library for its
-- excellent parsing combinators, which allow regular expressions to
-- be written as first-class objects that, when executed, can
-- immediately bind the constituents of the matched strings to
-- functions to produce, for instance, 'Token' data.
--
-- An annoying complication with this scanner is that the 6.035
-- specification requires that /all/ errors be reported, but Parsec
-- fails at the first sign of an error.  To solve this, portions of
-- the scanner are of the type 'ErrorScanner', which is an
-- 'ExceptionT'-wrapped 'Scanner' type.  Errors are caught using
-- structures of the form @p \<\<|>> scanFail (Just c)@, where
-- @(\<\<|>>)@ is @(\<|>)@ lifted to the 'ErrorScanner', @p@ is some
-- 'ErrorScanner', and @c@ is a character.  The @(\<\<|>>)@ operator
-- short-circuits on 'Exception's, and 'scanFail' raises as an
-- exception a 'TokenError' with the offending character and possibly
-- the expected character.
--
-- Due to the limited way in which the Parsec library exposes it's
-- implementation, it is not possible to obtain the list of expected
-- characters from within the monad, so the 'scanFail' operator
-- necessarily loses this information.  So that we can use normal
-- Parsec error handling but still be able to meet the 6.035
-- specification, the 'scanFail' operator can be turned on and off
-- (where off means the operator evaluates to 'mzero').  This is
-- toggled using the 'compatMode' option.
--
-- We have 'TokenType' and 'Token' be instances of 'Show' for
-- reasonable Parsec error messages and instances of 'Show6035' for
-- meeting the 6.035 specification.

module Scanner ( TokenType(..), Token(..), runScanner ) where

import Text.ParserCombinators.Parsec hiding (alphaNum)
import Text.Printf
import Control.Monad
import Control.Applicative hiding (many, (<|>))
import Data.Char (ord)
import Control.Exceptional
import Control.Monad.Trans

import CLI

---
--- Tokens
---

-- | Represents the type of the scanned token.  It is used in the
-- 'Token' type.
data TokenType = CharLiteral
               | IntLiteral
               | BooleanLiteral
               | StringLiteral
               | Identifier
               | Keyword
                 deriving (Eq)

-- | This is the type of a parsed token.  At least, that's how it
-- should be, except, for 6.035 compatibility mode, there is also a
-- 'TokenError' constructor to be able to accumulate errors during the
-- scanning phase.
data Token
    -- | The 'Token' constructor holds tokens which have been
    -- successfully parsed.
    = Token { tokenType :: TokenType
            , tokenPos :: SourcePos -- ^ The location of the start of
                                    -- the token in the source file.
            , tokenString :: String -- ^ Holds a textual
                                    -- representation of the token,
                                    -- which is unescaped for
                                    -- character and string literals.
            }
    -- | The 'TokenError' constructor is for accumulating errors in
    -- 6.035 compatibility mode.  It contains the location at which
    -- the error occured, maybe the offending character (which is
    -- 'Nothing' if the error is due to reaching the end of the
    -- input), and maybe the expected character (which is 'Nothing' if
    -- there is more than one possible expected character, for
    -- instance, in processing escape sequences in strings).
    | TokenError SourcePos (Maybe Char) (Maybe Char)

-- | Makes a parser which returns a 'Token' whose 'tokenString' is the
-- output of the given string-output parser.
makeToken :: TokenType -> Scanner String -> Scanner Token
makeToken restype parser = Token restype <$> getPosition <*> parser


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
                  c    -> [c]
          escStr :: String -> String
          escStr = (>>= escChar)
    show _ = error "use show6035"

instance Show TokenType where
    show CharLiteral = "character literal"
    show IntLiteral = "integer literal"
    show BooleanLiteral = "boolean literal"
    show StringLiteral = "string literal"
    show Identifier = "identifier"
    show Keyword = "keyword"


---
--- Scanner
---

-- | The Scanner type is a 'GenParser' which eats characters and
-- returns anything.
type Scanner = GenParser Char ScannerState
data ScannerState = ScannerState {
      scanner6035CompatMode :: Bool
    -- ^ This field enables or disables 'scanFail' if it is @True@ or
    -- @False@, respectively.
    }

-- | Runs the main 'scanner' on the input.  If 'compatMode' is passed
-- in with the 'CompilerOpts', then all of the errors are accumulated
-- and passed with the 'Token' list.  Otherwise, errors fail the
-- entire scanner and are returned as a 'ParseError'.
runScanner :: CompilerOpts
           -> String -- ^ Input file name
           -> String -- ^ Input file contents
           -> Either ParseError [Token]
runScanner opts ifname input
    = runParser scanner scanState ifname input
      where scanState = ScannerState
                        { scanner6035CompatMode=compatMode opts }

---
--- ErrorScanner
---

-- | 'ErrorScanner' is a 'Scanner' wrapped in an 'ExceptionalT' whose
-- errors are 'Tokens' so that we can accumulate 'ErrorToken's if we
-- are in 6.035 compatibility mode.
type ErrorScanner = ExceptionalT Token Scanner

-- | Puts result of 'scanError' of the argument into the 'Exception'
-- side of the 'ErrorScanner'.  This makes Parsec think the scanner
-- has not failed while short-circuiting normal operation of Parsec,
-- thus letting us catch the error later without losing Parsec's
-- state.
scanFail :: Maybe Char -> ErrorScanner a
scanFail mc = lift (scanError mc) >>= throwT

-- | Takes an 'ErrorScanner' and combines 'Success' and 'Exception'
-- into one stream.
catchErrorScanner :: ErrorScanner Token -> Scanner Token
catchErrorScanner = flip catchT id

-- | Takes maybe an expected character, checks if we're in 6.035
-- compatibility mode, and, if so, returns a 'TokenError' using the
-- 'makeTokenError' helper function.
scanError :: Maybe Char -> Scanner Token
scanError mc'
    = do s <- getState
         if scanner6035CompatMode s
           then makeTokenError mc'
           else mzero
    where
      -- | This 'Scanner' eats the offending character and returns a
      -- 'TokenError'.  Due to a wierd quirk of ANTLR, against which
      -- the 6.035 specification is defined, unexpected newline and
      -- tab characters do not increment the current position as
      -- expected, so a hack is built in to compensate.
      makeTokenError :: Maybe Char -> Scanner Token
      makeTokenError mc =
          do pos <- getPosition
             -- consume the offending character
             c <- optionMaybe anyChar
             -- dumb hack to satisfy 6.035 compatibility...
             let hack = case c of
                          Just '\t' -> 7
                          Just '\n' -> 1
                          _ -> 1
             setPosition (incSourceColumn pos hack)
             return $ TokenError pos c mc

---
--- Top-level scanners
---

-- | This is the top-level scanner.  It repeatedly eats whitespace and
-- scans with 'dctoken' to collect the 'Token's.
scanner :: Scanner [Token]
scanner = do whitespace
             manyTill (dctoken <* whitespace) eof

-- | This is the main token scanner!  Matches a token, and if it
-- can't, runs 'scanFail' for 6.035 compatibility mode.
dctoken :: Scanner Token
dctoken = keywords <|> boolLiteral <|> identifier <|> intLiteral
          <|> charLiteral <|> stringLiteral <|> symbolTokens
          <|> scanError Nothing

-- | This scanner matches the reserved keywords in decaf.
keywords :: Scanner Token
keywords = choice $ map keyword reservedWords
    where
      reservedWords :: [String]
      reservedWords
          = ["boolean", "break", "callout", "class", "continue"
            ,"else", "for", "if", "int", "return", "void", "while"]

-- | This scanner matches operators and punctuation symbols.
symbolTokens :: Scanner Token
symbolTokens = choice [makeToken Keyword (try $ string s) | s <- symbols]
    where
      -- This list of operators and punctuation is ordered so the
      -- prefixes of a symbol don't appear before it.
      symbols :: [String]
      symbols = ["{", "}", "(", ")", "[", "]", ";", ",",
                 "==", "=", "+=", "-=", "+", "-", "*", "/", "%",
                 "<=", ">=", "<", ">", "!=", "!", "&&", "||"]

-- | The 'identifier' scanner matches @alpha+(many alphaNum)@.
identifier :: Scanner Token
identifier = makeToken Identifier identifier'
    where identifier' = (:) <$> alpha <*> many alphaNum  <?> "identifier"

-- | Matches a hexadecimal, decimal, or binary literal.  Since finding
-- "0x" or "0b" could result in scanner failure, this scanner might
-- return a 'TokenError'.
intLiteral :: Scanner Token
intLiteral = catchErrorScanner $ hexLiteral <<|>> binLiteral <<|>> decLiteral
    where
      intLiteral' :: String -> Scanner Char -> ErrorScanner Token
      intLiteral' prefix digitParser
          = do pos <- lift getPosition
               _ <- lift $ try (string prefix)
               digit1 <- lift digitParser <<|>> scanFail Nothing
               digits <- lift $ many digitParser
               return $ Token IntLiteral pos (prefix ++ (digit1:digits))

      hexLiteral = intLiteral' "0x" hexDigit
      binLiteral = intLiteral' "0b" $ oneOf "01"
      decLiteral = lift $ makeToken IntLiteral $ many1 digit

-- | Matches @true@ or @false@.
boolLiteral :: Scanner Token
boolLiteral = boolReserved "true" <|> boolReserved "false"  <?> "boolean"
    where boolReserved s = makeToken BooleanLiteral (reserved s)

-- | Matches a character literal.  Escapes might fail, so uses an
-- 'ErrorScanner' internally.
charLiteral :: Scanner Token
charLiteral = catchErrorScanner $
   Token CharLiteral <$> lift getPosition
             <*> mbetween '\'' (return <$> dchar
                                <<|>> scanFail Nothing)

-- | Matches a string literal.  Escapes might fail, so uses an
-- 'ErrorScanner' internally.
stringLiteral :: Scanner Token
stringLiteral = catchErrorScanner $
   Token StringLiteral <$> lift getPosition
             <*> mbetween '"' (mmany dchar)

---
--- Helper scanners
---

-- | The 'alpha' scanner matches @[a-zA-Z_]@.
alpha :: Scanner Char
alpha = letter <|> char '_'     <?> "alpha"

alphaNum :: Scanner Char
alphaNum = alpha <|> digit        <?> "alphanumeric"

eol :: Scanner ()
eol = eof <|>  () <$ char '\n'  <?> "end of line"

-- | Matches sequences of whitespace and comments.
whitespace :: Scanner ()
whitespace = () <$ many (() <$ oneOf " \n\t"
                         <|> comment)
    where comment = do _ <- try $ string "//"
                       _ <- manyTill anyChar eol
                       return ()

-- | Matches a particular string as long as it's not followed by
-- alphaNum, hence establishing that the string is not some other
-- identifier.
reserved :: String -> Scanner String
reserved s = try (string s <* notFollowedBy alphaNum)

-- | Creates a scanner which matches a string as a keyword
keyword :: String -> Scanner Token
keyword s = makeToken Keyword $ reserved s

-- | Matches a character inside a character literal or string.  Since
-- escape codes can fail, this is an 'ErrorScanner'.
dchar :: ErrorScanner Char
dchar = do _ <- lift (char '\\') <<?>> "backslash"
           escapedChar <<|>> scanFail Nothing -- scanFail since ate backslash
        <<|>> (lift (satisfy isValidChar) <<?>> "valid non-quote character")
    where
      escapedTable = [('\'', '\''), ('"', '"'), ('\\', '\\'),
                      ('t', '\t'), ('n', '\n')]
      escapedChar :: ErrorScanner Char
      escapedChar = foldr1 (<<|>>) [r <$ lift (char c)
                                    | (c,r) <- escapedTable]
      isValidChar c = ord c >= 32
                      && ord c <= 126
                      && c `notElem` "'\""


---
--- Combinators for ErrorScanner
---

-- These are the same fixities as <?> and <|>, respectively.
infix 0 <<?>>
infixr 1 <<|>>

-- | This is like @(\<?>)@ for 'Scanner's but instead lifted to
-- 'ErrorScanner'.
(<<?>>) :: ErrorScanner a -> String -> ErrorScanner a
p <<?>> s = ExceptionalT (runExceptionalT p <?> s)


-- | This is like @(\<?>)@ for 'Scanner's but instead lifted to
-- 'ErrorScanner'.  Importantly, if p1 gives an 'Exception', then the
-- choice is short-circuited because Parsec will think that the parse
-- has succeeded.
(<<|>>) :: ErrorScanner a -> ErrorScanner a -> ErrorScanner a
p1 <<|>> p2 = ExceptionalT $ runExceptionalT p1 <|> runExceptionalT p2

-- | This is like 'between' (with one delimiter) lifted to be an
-- 'ErrorScanner', except the closing delimiter, if it doesn't match,
-- runs 'scanFail'.
mbetween :: Char -> ErrorScanner a -> ErrorScanner a
mbetween c p =
    do _ <- lift $ char c
       inside <- p
       _ <- lift (char c) <<|>> scanFail (Just c)
       return inside

-- | Like 'optionMaybe', but lifted to 'ErrorScanner'.
mOptionMaybe :: ErrorScanner a -> ErrorScanner (Maybe a)
mOptionMaybe p = (Just <$> p) <<|>> return Nothing

-- | Like 'many', but lifted to 'ErrorScanner'.
mmany :: ErrorScanner a -> ErrorScanner [a]
mmany p = do mx <- mOptionMaybe p
             case mx of
               Nothing -> return []
               Just x -> (x:) <$> mmany p
