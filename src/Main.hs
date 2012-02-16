module Main where

import IO
import System.Environment
import System.Exit
import CLI
import Data.Maybe (fromMaybe)
import Control.Monad
import Scanner
import Parser
import ScannerResultPrinter
import Data.List
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Error

main :: IO ()
main = do args <- getArgs
          opts <- compilerOpts args
          let ifname = fromMaybe "<stdin>" $ inputFile opts
          input <- case inputFile opts of
                     Just ifname -> readFile ifname
                     Nothing -> hGetContents stdin
          case target opts of
            TargetScan -> doScanFile opts ifname input
            TargetParse -> doParseFile opts ifname input
            _ -> error "No such target"


reportErr :: [String] -> ParseError -> IO ()
reportErr lines err = do putStrLn $ (show $ errorPos err) ++ ":"
                         putStrLn line
                         putStr errptr
                         putStrLn $ showErrorMessages "or" "unknown parse error"
                                      "expecting" "unexpected" "end of input"
                                      (errorMessages err)
    where line = lines !! (sourceLine pos - 1)
          errptr = replicate (sourceColumn pos - 1) ' '
                   ++ "^"
          pos = errorPos err

doScanFile opts ifname input
    = case runScanner opts ifname input of
        Left err -> reportErr (lines input) err
        Right v -> printScannerResult v

doParseFile opts ifname input
    = case runScanner opts ifname input of
        Left err -> do reportErr (lines input) err
                       exitWith $ ExitFailure 1
        Right v ->
            case getErrors v of
              [] -> case runDParser opts v of
                      Left err -> do reportErr (lines input) err
                                     exitWith $ ExitFailure 1
                      Right r -> do print r
                                    exitWith $ ExitSuccess
              errors -> do printScannerResult errors
                           exitWith $ ExitFailure 1
    where getErrors res
              = filter isTokenError res
          isTokenError (TokenError {}) = True
          isTokenError _ = False
