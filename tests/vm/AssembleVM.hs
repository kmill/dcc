module AssembleVM where

import IO hiding (try)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Control.Applicative hiding ((<|>), many)
import qualified Data.Map as M
import Data.Either

main :: IO ()
main = do let ifname="<stdin>"
          input <- getContents -- readFile
          case runScanner ifname input of
            Left err -> putStrLn $ reportErr (lines input) err
            Right tkns ->
              case toAssem tkns of
                Left err -> putStrLn $ reportAssemErr (lines input) err
                Right words -> do putStrLn $ show (length words) 
                                  mapM putStrLn (map show' words)
                                  return ()
  where show' (Word i) = show i

mnemonics :: [(String, Int)]
mnemonics = [ ("lit", 1)
            , ("neg", 2)
            , ("eqz", 3)
            , ("add", 4)
            , ("sub", 5)
            , ("mul", 6)
            , ("div", 7)
            , ("mod", 8)
            , ("lt", 9)
            , ("and", 10)
            , ("or", 11)
            , ("jmp", 20)
            , ("jnz", 21)
            , ("call", 22)
            , ("ret", 23)
            , ("exit", 24)
            , ("drop", 30)
            , ("swap", 31)
            , ("dup", 32)
            , ("store", 40)
            , ("load", 41)
            , ("print", 50)
            , ("input", 51)
            , ("debug", 2222)
            ]

data Assembled = Word Int
               | Ref SourcePos String
data AssemError = AssemNoLabel SourcePos String

toAssem :: [Token] -> Either AssemError [Assembled]
toAssem tkns = let f i labs [] res = (labs, res)
                   f i labs (tok:toks) res
                     = case tok of
                         Label pos str -> f i (M.insert str i labs) toks res
                         Number pos n -> f (i+1) labs toks (res ++ [Word n])
                         Symbol pos str ->
                           case lookup str mnemonics of
                             Just n -> f (i+1) labs toks (res ++ [Word n])
                             Nothing -> f (i+1) labs toks (res ++ [Ref pos str])
                   (labmap, assem) = f 0 M.empty tkns []
                   g (Word i) = Right $ Word i
                   g (Ref pos s) = case M.lookup s labmap of
                                     Just i -> Right $ Word i
                                     Nothing -> Left $ AssemNoLabel pos s
                   (errs, assem') = partitionEithers (map g assem)
               in case errs of
                    (err:_) -> Left err
                    [] -> Right assem'

type Scanner = GenParser Char ScannerState
data ScannerState = ScannerState

data Token = Label SourcePos String
           | Number SourcePos Int
           | Symbol SourcePos String
           deriving Show
             
alabel :: Scanner Token
alabel = Label <$> getPosition
         <*> try (many validchar <* char ':')
  where validchar = letter <|> char '_' <|> digit  <?> "alphanumeric"

alit :: Scanner Token
alit = Symbol <$> getPosition
       <*> ("lit" <$ char '$')
acall :: Scanner Token
acall = Symbol <$> getPosition
       <*> ("call" <$ char '@')
        
shorthand = alit <|> acall

anumber :: Scanner Token
anumber = Number <$> getPosition
          <*> (read <$> many1 digit)
asymbol :: Scanner Token
asymbol = Symbol <$> getPosition
          <*> (many1 alphaNum <* notFollowedBy alphaNum)
         
atoken = shorthand <|> alabel <|> anumber <|> asymbol

ascanner :: Scanner [Token]
ascanner = do whitespace
              manyTill (atoken <* whitespace) eof
             
runScanner :: String -> String -> Either ParseError [Token]
runScanner ifname input
    = runParser ascanner scanState ifname input
      where scanState = ScannerState

whitespace :: Scanner ()
whitespace = () <$ many (() <$ oneOf " \n\t"
                         <|> comment)
    where comment = do _ <- try $ string "//"
                       _ <- manyTill anyChar eol
                       return ()

eol :: Scanner ()
eol = eof <|>  () <$ char '\n'  <?> "end of line"
            
            
-- | This function formats an error so it has a nifty carat under
-- where the error occured.
reportErr :: [String] -- ^ The lines from the source file
          -> ParseError -- ^ The parse error to format
          -> String
reportErr ls err
     = show (errorPos err) ++ ":" ++ "\n"
       ++ line ++ "\n"
       ++  errptr
       ++  (showErrorMessages "or" "unknown parse error"
                      "expecting" "unexpected" "end of input"
                      (errorMessages err)) ++ "\n"
    where line = ls !! (sourceLine pos - 1)
          errptr = replicate (sourceColumn pos - 1) ' '
                   ++ "^"
          pos = errorPos err

reportAssemErr ls (AssemNoLabel pos s)
     = show pos ++ ":" ++ "\n"
       ++ line ++ "\n"
       ++  errptr
       ++  "No such label " ++ show s
    where line = ls !! (sourceLine pos - 1)
          errptr = replicate (sourceColumn pos - 1) ' '
                   ++ "^"
