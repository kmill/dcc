-- | The 'CLI' module is for parsing decaf command line arguments to
-- meet the 6.035 specification.

module CLI ( compilerOpts, CompilerOpts(..), TargetFlag(..)) where

import System.Console.GetOpt
import System.Exit

-- | This type contains the result of parsing command line arguments
-- | for the decaf compiler.
data CompilerOpts
    = CompilerOpts { inputFile :: Maybe String
                   -- ^ If specified, the file present on the command line.
                   , outputFile :: Maybe String
                   -- ^ If specified, the file given by @-o@ or @--out@.
                   , target :: TargetFlag
                   -- ^ The target given by @-t@ or @--target@.
                   , debugMode :: Bool
                   -- ^ Whether @--debug@ was present.
                   , compatMode :: Bool
                   -- ^ Whether @--compat@ was present, which turns on
                   -- 6.035 compatibility mode.
                   , helpMode :: Bool
                   -- ^ Whether @-h@ or @--help@ was specified, which
                   -- immediately quits and provides usage
                   -- information.
                   }
      deriving (Show)

defaultOptions :: CompilerOpts
defaultOptions
    = CompilerOpts { inputFile = Nothing
                   , outputFile = Nothing
                   , target = TargetDefault
                   , debugMode = False
                   , compatMode = False
                   , helpMode = False
                   }

-- | This type represents the possible actions to do with the input
-- file.
data TargetFlag = TargetScan -- ^ Given by @scan@.
                | TargetParse -- ^ Given by @parse@.
                | TargetInter -- ^ Given by @inter@.
                | TargetLowIR -- ^ Given by @lowir@.
                | TargetCodeGen -- ^ Given by @codegen@.
                | TargetDefault -- ^ The default value if no target is given.
                  deriving (Show)

options :: [OptDescr (CompilerOpts -> CompilerOpts)]
options =
    [ Option ['o']  ["out"]     (ReqArg outfile' "FILE")    "output FILE"
    , Option ['t']  ["target"]  (ReqArg target' "TARGET")   "set target type"
    , Option []     ["debug"]   (NoArg debug')              "enables debug mode"
    , Option []  ["compat"]  (NoArg compat')             "enables compatibility mode with 6.035 output spec"
    , Option ['h']  ["help"]    (NoArg help')               "prints this usage information"
    ]
    where outfile' s opts = opts { outputFile = Just s }
          target' t opts = opts { target = targetOpt t }
          debug' opts = opts { debugMode = True }
          compat' opts = opts { compatMode = True }
          help' opts = opts { helpMode = True }

targetOpt :: String -> TargetFlag
targetOpt s
    = case s of
        "scan" -> TargetScan
        "scanner" -> TargetScan
        "parse" -> TargetParse
        "inter" -> TargetInter
        "lowir" -> TargetLowIR
        "codegen" -> TargetCodeGen
        "assembly" -> TargetCodeGen
        _ -> TargetDefault


-- | Takes an argument list and gives a 'CompilerOpts'.  If there's a
-- parse error or help request, this function uses 'System.Exit' to
-- halt the entire program (hence the type being @IO CompilerOpts@).
compilerOpts :: [String] -> IO CompilerOpts
compilerOpts argv
    = case getOpt argorder options argv of
        (o,_,[]) -> let opts = foldl (flip id) defaultOptions o
                    in case helpMode opts of
                         True -> do putStr $ usageInfo header options
                                    exitSuccess
                         False -> return opts
        (_,_,errs) -> do putStr (concat errs ++ usageInfo header options)
                         exitWith $ ExitFailure 1
    where header = "Usage: dcc [OPTIONS...] source"
          argorder = ReturnInOrder (\s opts -> opts { inputFile = Just s })
