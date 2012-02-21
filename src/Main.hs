-- | This is where the magic starts.

module Main where

import System.Environment
import System.Exit
import CLI
import Data.Maybe (fromMaybe)
import Control.Monad
import Scanner
import Parser
import ScannerResultPrinter
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Error

-- | The main entry point to @dcc@.  See 'CLI' for command line
-- arguments.
main :: IO ()
main = do args <- getArgs
          opts <- compilerOpts args
          let ifname = fromMaybe "<stdin>" $ inputFile opts
          input <- case inputFile opts of
                     Just fname -> readFile fname
                     Nothing -> getContents -- of stdin
          case target opts of
            TargetScan -> doScanFile opts ifname input
            TargetParse -> doParseFile opts ifname input
            _ -> error "No such target"


-- | This function formats an error so it has a nifty carat under
-- where the error occured.
reportErr :: [String] -- ^ The lines from the source file
          -> ParseError -- ^ The parse error to format
          -> IO ()
reportErr ls err
    = do putStrLn $ show (errorPos err) ++ ":"
         putStrLn line
         putStr errptr
         putStrLn $ showErrorMessages "or" "unknown parse error"
                      "expecting" "unexpected" "end of input"
                      (errorMessages err)
    where line = ls !! (sourceLine pos - 1)
          errptr = replicate (sourceColumn pos - 1) ' '
                   ++ "^"
          pos = errorPos err

-- | Perfoms the actions for the @scan@ target.
doScanFile :: CompilerOpts -> String -> String -> IO ()
doScanFile opts ifname input
    = case runScanner opts ifname input of
        Left err -> reportErr (lines input) err
        Right v -> printScannerResult v

-- | Perfoms the actions for the @parse@ target.
doParseFile :: CompilerOpts -> String -> String -> IO ()
doParseFile opts ifname input
    = case runScanner opts ifname input of
        Left err -> do reportErr (lines input) err
                       exitWith $ ExitFailure 1
        Right v ->
            case getErrors v of
              [] -> case runDParser opts ifname v of
                      Left err ->
                          do reportErr (lines input) err
                             exitWith $ ExitFailure 1
                      Right r ->
                          do unless (compatMode opts) $ print r
                             exitSuccess
              errors -> do printScannerResult errors
                           exitWith $ ExitFailure 1
    where getErrors = filter isTokenError
          isTokenError (TokenError {}) = True
          isTokenError _ = False
