module CLI ( compilerOpts, CompilerOpts(..), TargetFlag(..)) where

import System.Console.GetOpt
import System.Exit

data CompilerOpts = CompilerOpts { inputFile :: Maybe String
                                 , outputFile :: Maybe String
                                 , target :: TargetFlag
                                 , debugMode :: Bool
                                 , compatMode :: Bool
                                 }
                    deriving (Show)

defaultOptions = CompilerOpts { inputFile = Nothing
                              , outputFile = Nothing
                              , target = TargetDefault
                              , debugMode = False
                              , compatMode = False
                              }


data TargetFlag = TargetScanner
                | TargetParse
                | TargetInter
                | TargetLowIR
                | TargetCodeGen
                | TargetDefault
                  deriving (Show)

options :: [OptDescr (CompilerOpts -> CompilerOpts)]
options =
    [ Option ['o']  ["out"]     (ReqArg outfile' "FILE")    "output FILE"
    , Option ['t']  ["target"]  (ReqArg target' "TARGET")   "set target type"
    , Option []     ["debug"]   (NoArg debug')              "enables debug mode"
    , Option ['c']  ["compat"]  (NoArg compat')             "enables compatibility mode with 6.035 output spec"
    ]
    where outfile' s opts = opts { outputFile = Just s }
          target' t opts = opts { target = targetOpt t }
          debug' opts = opts { debugMode = True }
          compat' opts = opts { compatMode = True }

targetOpt :: String -> TargetFlag
targetOpt s
    = case s of
        "scan" -> TargetScanner
        "scanner" -> TargetScanner
        "parse" -> TargetParse
        "inter" -> TargetInter
        "lowir" -> TargetLowIR
        "codegen" -> TargetCodeGen
        "assembly" -> TargetCodeGen
        _ -> TargetDefault



compilerOpts :: [String] -> IO CompilerOpts
compilerOpts argv
    = case getOpt argorder options argv of
        (o,_,[]) -> return $ foldl (flip id) defaultOptions o
        (_,_,errs) -> do putStr (concat errs ++ usageInfo header options)
                         exitWith $ ExitFailure 1
    where header = "Usage: dcc [OPTIONS...] source"
          argorder = ReturnInOrder (\s opts -> opts { inputFile = Just s })
