-- | The 'CLI' module is for parsing decaf command line arguments to
-- meet the 6.035 specification.

module CLI ( compilerOpts, CompilerOpts(..), TargetFlag(..), hasOptFlag, OptFlags) where

import System.Console.GetOpt
import System.Exit
import qualified Data.Set as S
import Data.Maybe
import Data.List
import Data.List.Utils(split)

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
                   , optMode :: OptFlags
                   -- ^ Which optimizations to use.
                   , macMode :: Bool
                   , regAllocMode :: Bool
                   , numThreads :: !Int
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
                   , optMode = defaultOptFlags
                   , macMode = False
                   , regAllocMode = False
                   , numThreads = 12
                   }

-- | This type represents the possible actions to do with the input
-- file.
data TargetFlag = TargetScan -- ^ Given by @scan@.
                | TargetParse -- ^ Given by @parse@.
                | TargetInter -- ^ Given by @inter@.
                | TargetMidIR -- ^ Given by @midir@.
                | TargetMidIRC -- ^ Given by @midirc@
                | TargetLowIR -- ^ Given by @lowir@.
                | TargetCodeGen -- ^ Given by @codegen@.
                | TargetDefault -- ^ The default value if no target is given.
                  deriving (Show, Eq)

type OptFlags = S.Set String

defaultOptFlags :: OptFlags
defaultOptFlags = S.empty

hasOptFlag :: String -> OptFlags -> Bool
hasOptFlag name opts = name `S.member` opts
          
optimizations =
    [ ("cse", "Constant Subexpression Elimination")
    , ("copyprop", "Copy Propagation")
    , ("condelim", "Conditional Elimination")
    , ("constprop", "Constant Propagation")
--    , ("nzp", "-/0/+ Analysis")
    , ("deadcode", "Dead Code Elimination")
    , ("blockelim", "Block Elimination")
    , ("flat", "Flatten Optimization")
    , ("unflat", "Unflatten Optimization")
    , ("tailcall", "Tailcall Elimination")
    , ("licm", "Loop Invariant Code Motion")
    , ("parallelize", "Automatic Loop Parallelization")
    , ("winnowstr", "Removes unused strings")
    , ("deadcodeasm", "Dead code elimination on assembly")
    , ("colorspills", "Recolor spills in assembly")
    , ("betterifyasm", "Constant/copy propagation on assembly")
    , ("blockelimasm", "Block elimination on assembly")
    ]

optimizationClasses =
    [ ("all", map fst optimizations)
    , ("basic", [ "constprop"
                , "deadcode"
                , "blockelim"
                , "winnowstr"])
    , ("asm", [ "deadcodeasm" 
              , "colorspills"
              , "betterifyasm"
              , "blockelimasm"]) ]

showOptimizations :: String
showOptimizations = unlines $ map showOpt optimizations
    where maxnamelength = maximum $ map (length . fst) optimizations
          showOpt (name, desc) = replicate (maxnamelength - length name) ' '
                                 ++ name ++ " : " ++ desc

showOptClasses :: String
showOptClasses = "\n Optimization classes which can be passed to --opt:\n"
                 ++ (unlines $ map showOptClass optimizationClasses)
    where maxnamelength = max 10 (maximum $ map (length . fst) optimizationClasses)
          showOptClass (name, opts) = replicate (maxnamelength - length name) ' '
                                      ++ name ++ " : " ++ optlist opts
          optlist opts = prelines $ map (intercalate " ") $ intoFive opts
          prelines = intercalate ("\n   " ++ replicate maxnamelength ' ')
          intoFive :: [a] -> [[a]]
          intoFive list | null list = []
                        | length list < 5 = [list]
                        | otherwise = let (xs,ys) = splitAt 5 list
                                      in xs:(intoFive ys)

options :: [OptDescr (CompilerOpts -> CompilerOpts)]
options =
    [ Option ['o']  ["out"]     (ReqArg outfile' "FILE")    "output FILE"
    , Option ['t']  ["target"]  (ReqArg target' "TARGET")   ("Set target type:\n" ++
                                                             "\t   scan : Scans the input file\n" ++
                                                             "\t  parse : Parses the input file\n" ++
                                                             "\t  midir : Outputs a graph of the mid IR\n" ++
                                                             "\t  lowir : Outputs a graph of the low IR\n" ++
                                                             "\tcodegen : Outputs the compiled assembly code" )
    , Option ['d']     ["debug"]   (NoArg debug')              "Enables debug mode"
    , Option ['m']     ["mac"]   (NoArg mac')              "Enables Mac OS X mode"
    , Option ['c']     ["compat"]  (NoArg compat')             "Enables compatibility mode with 6.035 output spec"
    , Option ['h']  ["help"]    (NoArg help')               "Prints this usage information"
    , Option ['p']  ["numthreads"] (ReqArg numthreads' "NUM") ("Sets the number of threads used by parallelize (default: " ++ show (numThreads defaultOptions) ++ ")")
    , Option ['r']  ["regalloc"] (NoArg regalloc')          "Enables the register allocator"
    , Option ['O']     ["opt"]     (ReqArg optimize' "OPTIMIZATION") ("Enables optimizations:\n"
                                                                      ++ showOptimizations
                                                                      ++ "\nPrefixing an optimization with '-' disables it."
                                                                      ++ "\nall/none enables/disables ALL optimizations.")
    ]
    where outfile' s opts = opts { outputFile = Just s }
          target' t opts = opts { target = targetOpt t }
          debug' opts = opts { debugMode = True }
          compat' opts = opts { compatMode = True }
          help' opts = opts { helpMode = True }
          optimize' t opts
            = opts { optMode = foldl (flip id) (optMode opts)
                               [optOpt p | p <- split "," t] }
          mac' opts = opts { macMode = True }
          regalloc' opts = opts { regAllocMode = True }
          numthreads' nt opts = opts { numThreads = fst $ fromMaybe (error "That's not a number passed to --numthreads") $ listToMaybe $ reads nt }


targetOpt :: String -> TargetFlag
targetOpt s
    = case s of
        "scan" -> TargetScan
        "scanner" -> TargetScan
        "parse" -> TargetParse
        "inter" -> TargetInter
        "midir" -> TargetMidIR
        "midirc" -> TargetMidIRC
        "lowir" -> TargetLowIR
        "codegen" -> TargetCodeGen
        "assembly" -> TargetCodeGen
        _ -> TargetDefault

optOpt :: String -> OptFlags -> OptFlags
optOpt s opts
  = case s of
      "none" -> S.empty
      '-':name -> opts S.\\ optLookup name
      name -> opts `S.union` optLookup name
    where optLookup name = case lookup name optimizationClasses of
                             Just s -> S.fromList s
                             Nothing -> case lookup name optimizations of
                                          Just _ -> S.singleton name
                                          Nothing -> S.empty

-- | Takes an argument list and gives a 'CompilerOpts'.  If there's a
-- parse error or help request, this function uses 'System.Exit' to
-- halt the entire program (hence the type being @IO CompilerOpts@).
compilerOpts :: [String] -> IO CompilerOpts
compilerOpts argv
    = case getOpt argorder options argv of
        (o,_,[]) -> let opts = foldl (flip id) defaultOptions o
                    in case helpMode opts of
                         True -> do putStr $ usageInfo header options
                                    putStr $ showOptClasses
                                    exitSuccess
                         False -> return opts
        (_,_,errs) -> do putStr (concat errs ++ usageInfo header options)
                         exitWith $ ExitFailure 1
    where header = "Usage: dcc [OPTIONS...] source"
          argorder = ReturnInOrder (\s opts -> opts { inputFile = Just s })
