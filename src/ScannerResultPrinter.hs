module ScannerResultPrinter(printScannerResult) where

import Text.Printf
import IO
import Text.ParserCombinators.Parsec.Pos
import Scanner
import Data.Maybe (fromMaybe)
import Data.Char (ord)

printScannerResult :: [Token] -> IO ()
printScannerResult (t:ts) = do putStrLn $ show6035 t
                               printScannerResult ts
printScannerResult [] = return ()

class Show6035 a where
    show6035 :: a -> String

-- Wraps the second string with two copies of the first string.
quotify :: String -> String -> String
quotify q s = q ++ s ++ q

instance Show6035 Token where
    show6035 (TokenError pos c mc)
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
                                  
    show6035 x = ln ++ tokType ++ " " ++ tokStr
        where ln = show $ sourceLine $ tokenPos x
              -- gives a textual representation of the type field
              tokType = case tokenType x of
                          Keyword -> ""
                          t -> " " ++ (show6035 t)
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

instance Show6035 TokenType where
    show6035 CharLiteral = "CHARLITERAL"
    show6035 IntLiteral = "INTLITERAL"
    show6035 BooleanLiteral = "BOOLEANLITERAL"
    show6035 StringLiteral = "STRINGLITERAL"
    show6035 Identifier = "IDENTIFIER"
    show6035 Keyword = "KEYWORD"
