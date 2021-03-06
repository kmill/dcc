-- | This is where the magic starts.

module Main where

import IO
import System.Environment
import System.Exit
import System.FilePath
import CLI
import Data.Maybe (fromMaybe)
import Control.Monad
import Scanner
import Parser
import Util.ScannerResultPrinter
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Error
import SemanticCheck
import SymbolTable
import Text.Printf
import Control.Unify
import Compiler.Hoopl.Fuel
import Data.List
import AST

import Debug.Trace

import qualified IR
import qualified MidIR
import Dataflow
import AsmDataflow
import qualified CodeGenerate
import qualified RegAlloc.Allocator as RegisterAllocator
import qualified RegAlloc.SimpleRegAlloc as SimpleRegAlloc
import RegAlloc.BakeSpills
import Assembly
import qualified LoopAnalysis

-- | The main entry point to @dcc@.  See 'CLI' for command line
-- arguments.
main :: IO ()
main = do args <- getArgs
          opts <- compilerOpts args
          when (debugMode opts) $ do
            hPutStrLn stderr $ "Compiler options:\n" ++ show opts
          let ifname = fromMaybe "<stdin>" $ inputFile opts
          input <- case inputFile opts of
                     Just fname -> readFile fname
                     Nothing -> getContents -- of stdin
          let tokens = doScanFile opts ifname input
              dprogram = doParseFile opts ifname input tokens
              ast = doCheckFile opts ifname input dprogram
              midir = doMidIRFile opts ifname input ast
              midirc = doMidIRFile opts ifname input ast
              lowir = do midir' <- midir
                         doLowIRFile opts ifname input midir'
          outFile <- return $ case outputFile opts of
            Just fn -> fn
            Nothing -> case inputFile opts of
                         Just ifname -> replaceExtension ifname ".s"
                         Nothing -> "a.out.s"
          let tgt = case target opts of
                      TargetDefault -> TargetCodeGen
                      x -> x
          case tgt of
            TargetScan -> case tokens of
              Left err -> do (putStrLn err)
                             exitWith $ ExitFailure 1
              Right v -> putStrLn $ printScannerResult v
            TargetParse -> case dprogram of
              Left err -> do (putStrLn err)
                             exitWith $ ExitFailure 1
              Right r -> unless (compatMode opts) $ print r
            TargetInter -> case ast of
              Left err -> do (putStrLn err)
                             exitWith $ ExitFailure 1
              Right x -> do if debugMode opts then print x else return ()
            TargetMidIR -> case IR.runGM midir of
              Left err -> do (putStrLn err)
                             exitWith $ ExitFailure 1
              Right midir -> putStrLn $ IR.midIRToGraphViz midir
            TargetMidIRC -> case IR.runGM midir of
              Left err -> do (putStrLn err)
                             exitWith $ ExitFailure 1
              Right midir -> putStrLn $ CodeGenerate.midIRToC midir
            TargetLowIR -> case IR.runGM lowir of
              Left err -> do (putStrLn err)
                             exitWith $ ExitFailure 1
              Right lir -> putStrLn $ CodeGenerate.lowIRToGraphViz lir 
            TargetCodeGen ->
                case IR.runGM lowir of
                  Left err -> do
                             putStrLn err
                             exitWith $ ExitFailure 1
                  Right lir -> let asm = CodeGenerate.lowIRToAsm lir opts
                               in do writeFile outFile $ unlines asm
                                     when (debugMode opts) $ do
                                       putStrLn $ intercalate "\n" asm
            _ -> error "No such target"
            
-- | Perfoms the actions for the @scan@ target.
doScanFile :: CompilerOpts -> String -> String -> Either String [Token]
doScanFile opts ifname input
  = case runScanner opts ifname input of
    Left err -> Left (reportErr (lines input) err)
    Right v2 -> Right v2
    
-- | Perfoms the actions for the @parse@ target.
doParseFile :: CompilerOpts -> String -> String -> Either String [Token] -> Either String DProgram
doParseFile opts ifname input toks
  = case toks of
    Left err -> Left err
    Right v ->
      case getErrors v of
        [] -> case runDParser opts ifname v of
          Left err -> Left (reportErr (lines input) err)
          Right r -> Right r
        errors -> Left (printScannerResult errors)
    where getErrors = filter isTokenError
          isTokenError (TokenError {}) = True
          isTokenError _ = False
      
-- | Performs the actions for the @inter@ target. 
doCheckFile :: CompilerOpts -> String -> String -> Either String DProgram
            -> Either String (HDProgram Int)
doCheckFile opts ifname input r
  = case r of
    Left err -> Left err
    Right v ->
      case doSemanticCheck v of
        Left (udata, errors) ->
          Left ("Semantic errors:\n" ++ "\n" ++ (intercalate "\n" [(showSemError (lines input) udata e) | e <- errors]))
        Right x -> Right (makeHybridAST v)
        
-- | Performs the actions for the @midir@ and @c@ target.
doMidIRFile :: CompilerOpts -> String -> String -> Either String (HDProgram Int)
               -> IR.GM (Either String (IR.MidIRRepr))
doMidIRFile opts ifname input ast
  = case ast of
    Left err -> return $ Left err
    Right hast -> do mir <- MidIR.generateMidIR hast
                     mir <- runWithFuel maxBound $ (performDataflowAnalysis opts mir)
                     return $ Right mir
                    
doLowIRFile :: CompilerOpts -> String -> String -> Either String IR.MidIRRepr 
               -> IR.GM (Either String LowIRRepr)
doLowIRFile opts ifname input midir
    = case midir of        
        Left err -> return $ Left err
        Right m -> do let itermap = LoopAnalysis.findIterationMap m
                      lowir <- CodeGenerate.toAss opts m
                      lowir <- (if debugMode opts then return else allocator itermap) lowir
                      lowir <- runWithFuel maxBound $ do
                                 lowir <- performAsmDataflowAnalysis opts lowir
                                 lowir <- (if debugMode opts then return else performBakeSpills opts) lowir
                                 return lowir
                      return $ Right lowir
      where allocator itermap
              = case regAllocMode opts || (hasOptFlag "regalloc" (optMode opts)) of
                  True -> RegisterAllocator.regAlloc itermap
                  False -> SimpleRegAlloc.regAlloc
                 
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
showSemError ls ud (SemRangeCheckError pos)
    = printf "%s\nOut of bounds for a 64-bit integer.\n"
      (posToLineView ls pos)
          
posToLineView :: [String] -> SourcePos -> String
posToLineView ls pos
    = (show pos) ++ "\n" ++ line ++ "\n" ++ errptr
    where line = ls !! (sourceLine pos - 1)
          errptr = replicate (sourceColumn pos - 1) ' '
                   ++ "^"
