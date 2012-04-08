-- | This is where the magic starts.

module Main where

import System.Environment
import System.Exit
import System.FilePath
import CLI
import Data.Maybe (fromMaybe)
import Control.Monad
import Scanner
import Parser
import ScannerResultPrinter
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Error
import SemanticCheck
import SymbolTable
import Text.Printf
import Unify
import CodeGenerate
import MidIR
import LowIR
import RegisterAllocator
import Assembly
import Assembly2
import Dataflow
import Compiler.Hoopl.Fuel

import qualified IR2
import qualified MidIR2

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
            TargetMidIR -> doMidIRFile opts ifname input
            TargetLowIR -> doLowIRFile opts ifname input
            TargetDefault -> doGenerateCode opts ifname input
            TargetCodeGen -> doGenerateCode opts ifname input
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
                             exitWith $ ExitFailure 2
                      Right r ->
                          do unless (compatMode opts) $ print r
                             exitSuccess
              errors -> do printScannerResult errors
                           exitWith $ ExitFailure 1
    where getErrors = filter isTokenError
          isTokenError (TokenError {}) = True
          isTokenError _ = False

-- | Performs the actions for the @inter@ target. 
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
                             exitWith $ ExitFailure 2
                      Right r ->
                          case doSemanticCheck r of
                            Right x -> do if debugMode opts then 
                                              print (makeHybridAST r) else --putStrLn ((show x) ++ "\nok.") 
                                              return ()
                            Left (udata, errors) ->
                                do putStrLn "Semantic errors:"
                                   putStrLn ""
                                   sequence_ [putStrLn (showSemError (lines input) udata e)
                                              | e <- errors]
                                   exitWith $ ExitFailure 4
              errors -> do printScannerResult errors
                           exitWith $ ExitFailure 1
    where getErrors = filter isTokenError
          isTokenError (TokenError {}) = True
          isTokenError _ = False

doMidIRFile :: CompilerOpts -> String -> String -> IO ()
doMidIRFile opts ifname input 
    = case runScanner opts ifname input of
        Left err -> do reportErr (lines input) err
                       exitWith $ ExitFailure 1
        Right v ->
            case getErrors v of
              [] -> case runDParser opts ifname v of
                      Left err ->
                          do reportErr (lines input) err
                             exitWith $ ExitFailure 2
                      Right r ->
                          case doSemanticCheck r of
                            Right _ -> let hast = makeHybridAST r
                                           mmidir = do mir <- MidIR2.generateMidIR hast
                                                       mir <- runWithFuel 2222222 $ performDataflowAnalysis mir
                                                       return mir
                                           midir = IR2.runGM mmidir
                                       in do 
                                         putStrLn $ IR2.midIRToGraphViz midir
                            Left (udata, errors) ->
                                do putStrLn "Semantic errors:"
                                   putStrLn ""
                                   sequence_ [putStrLn (showSemError (lines input) udata e)
                                              | e <- errors]
                                   exitWith $ ExitFailure 4
              errors -> do printScannerResult errors
                           exitWith $ ExitFailure 1
    where getErrors = filter isTokenError
          isTokenError (TokenError {}) = True
          isTokenError _ = False

doLowIRFile :: CompilerOpts -> String -> String -> IO ()
doLowIRFile opts ifname input 
    = case runScanner opts ifname input of
        Left err -> do reportErr (lines input) err
                       exitWith $ ExitFailure 1
        Right v ->
            case getErrors v of
              [] -> case runDParser opts ifname v of
                      Left err ->
                          do reportErr (lines input) err
                             exitWith $ ExitFailure 2
                      Right r ->
                          case doSemanticCheck r of
                            Right _ -> let hast = makeHybridAST r
                                           midir = generateMidIR hast
                                           lowirSymb = toLowIR (optMode opts) midir
                                           lowir = destroySymbRegs lowirSymb
                                       in do
                                         --putStrLn $ show lowir
                                         if (debugMode opts) then
                                           putStrLn $ lowIRtoGraphViz lowir 
                                           else
                                           putStrLn $ lowIRtoGraphViz lowirSymb
                            Left (udata, errors) ->
                                do putStrLn "Semantic errors:"
                                   putStrLn ""
                                   sequence_ [putStrLn (showSemError (lines input) udata e)
                                              | e <- errors]
                                   exitWith $ ExitFailure 4
              errors -> do printScannerResult errors
                           exitWith $ ExitFailure 1
    where getErrors = filter isTokenError
          isTokenError (TokenError {}) = True
          isTokenError _ = False

-- | Generates unoptimized code for the @codegen@ target
doGenerateCode :: CompilerOpts -> String -> String -> IO ()
doGenerateCode opts ifname input 
    = case runScanner opts ifname input of
        Left err -> do reportErr (lines input) err
                       exitWith $ ExitFailure 1
        Right v ->
            case getErrors v of
              [] -> case runDParser opts ifname v of
                      Left err ->
                          do reportErr (lines input) err
                             exitWith $ ExitFailure 2
                      Right r ->
                          case doSemanticCheck r of
                            Right x -> let hast = makeHybridAST r
                                           midir = generateMidIR hast
                                           lowirSymb = toLowIR (optMode opts) midir
                                           lowir = destroySymbRegs lowirSymb
                                           code = runGenerateCode (makeHybridAST r) ifname 
                                           outFile = case outputFile opts of
                                             Just fn -> fn
                                             Nothing -> replaceExtension ifname ".s"
                                       in do 
                                         if  debugMode opts  
                                           then putStrLn $ (unlines $ lowIRReprCode lowir) ++ "\nOLD CODE: \n" ++ (show code) else return ()
                                         writeFile outFile  (unlines $ lowIRReprCode lowir)
                            Left (udata, errors) ->
                                do putStrLn "Semantic errors:"
                                   putStrLn ""
                                   sequence_ [putStrLn (showSemError (lines input) udata e)
                                              | e <- errors]
                                   exitWith $ ExitFailure 4
              errors -> do printScannerResult errors
                           exitWith $ ExitFailure 1
    where getErrors = filter isTokenError
          isTokenError (TokenError {}) = True
          isTokenError _ = False

showSemError :: [String] -> UnifierData DUType -> SemError -> String
showSemError ls ud (SemUnificationError uerr)
    = case uerr of
        UHeadError x y -> printf "%s\nCannot unify \"%s\" and \"%s\"\n"
                          (if xpos == ypos
                           then (posToLineView ls xpos)
                           else ((posToLineView ls xpos) ++ "\n"
                                 ++ (posToLineView ls ypos)))
                          (showDUTerm x')
                          (showDUTerm y')
            where x' = expandTerm x env
                  y' = expandTerm y env
                  xpos = duTermPos x
                  ypos = duTermPos y
        UOccursError v x -> printf "Type variable %s occurs in \"%s\"\n" -- TODO
                            (show v) (showDUTerm x')
            where x' = expandTerm x env
        UMismatchedLengths x y ->
            printf "%s\n%s\nMismatched number of arguments.\n"
            (posToLineView ls (duTermPos x)) (posToLineView ls (duTermPos y))
    where env = unifierEnv ud
showSemError ls ud (SemDupDef pos name)
    = printf "%s\nDuplicate definition of %s.\n"
      (posToLineView ls pos) (show name)
showSemError ls ud (SemUnboundError pos name typ)
    = printf "%s\nUnbound identifier %s.  Inferred type is \"%s\".\n"
      (posToLineView ls pos) (show name) (showDUTerm typ')
    where typ' = expandTerm typ (unifierEnv ud)
showSemError ls ud (SemBreakOutsideLoop pos)
    = printf "%s\nBreak statement outside of for loop.\n"
      (posToLineView ls pos)
showSemError ls ud (SemContinueOutsideLoop pos)
    = printf "%s\nContinue statement outside of for loop.\n"
      (posToLineView ls pos)
showSemError ls ud (SemNoMainError pos)
    = printf "%s\nProgram is missing a main method.\n"
      (posToLineView ls pos)
showSemError ls ud (SemNotScalarError t pos)
    = printf "%s%s\nType must be a scalar, not \"%s\".\n"
      (case t of
         Var _ -> (posToLineView ls (duTermPos t)) ++ "\n"
         _ -> "")
      (posToLineView ls pos)
      (showDUTerm t)
showSemError ls ud (SemArraySizeError pos)
    = printf "%s\nArray must have positive length.\n"
      (posToLineView ls pos)
          
posToLineView :: [String] -> SourcePos -> String
posToLineView ls pos
    = (show pos) ++ "\n" ++ line ++ "\n" ++ errptr
    where line = ls !! (sourceLine pos - 1)
          errptr = replicate (sourceColumn pos - 1) ' '
                   ++ "^"
