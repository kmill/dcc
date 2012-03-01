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
import SemanticCheck
import Text.Printf
import Unify

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
            TargetInter -> doCheckFile opts ifname input
            TargetDefault -> doParseFile opts ifname input
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

doCheckFile :: CompilerOpts -> String -> String -> IO ()
doCheckFile opts ifname input
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
                          case doSemanticCheck r of
                            Right x -> do putStrLn (show x)
                                          putStrLn "ok."
                            Left (udata, errors) ->
                                do putStrLn "Semantic errors:"
                                   putStrLn ""
                                   sequence_ [putStrLn (showSemError (lines input) udata e)
                                              | e <- errors]
                                   exitWith $ ExitFailure 1
              errors -> do printScannerResult errors
                           exitWith $ ExitFailure 1
    where getErrors = filter isTokenError
          isTokenError (TokenError {}) = True
          isTokenError _ = False

showSemError :: [String] -> UnifierData DUType -> SemError -> String
showSemError ls ud (SemUnificationError uerr)
    = case uerr of
        UHeadError x y -> printf "%s\n%s\nCannot unify \"%s\" and \"%s\"\n"
                          (posToLineView ls (duTermPos x)) (posToLineView ls (duTermPos y)) (showDUTerm x) (showDUTerm y)
        UOccursError v x -> printf "Type variable %s occurs in \"%s\"\n" -- TODO
                            (show v) (showDUTerm x')
            where x' = expandTerm x env
    where env = unifierEnv ud
showSemError ls ud (SemDupDef pos name)
    = printf "%s\nDuplicate definition of %s.\n"
      (posToLineView ls pos) (show name)
showSemError ls ud (SemUnboundError pos name typ)
    = printf "%s\nUnbound identifier %s.  Inferred type is \"%s\".\n"
      (posToLineView ls pos) (show name) (showDUTerm typ')
    where typ' = expandTerm typ (unifierEnv ud)
          
posToLineView :: [String] -> SourcePos -> String
posToLineView ls pos
    = (show pos) ++ "\n" ++ line ++ "\n" ++ errptr
    where line = ls !! (sourceLine pos - 1)
          errptr = replicate (sourceColumn pos - 1) ' '
                   ++ "^"
