module CodeGenerate where

import qualified Data.Map as Map 
import Data.Int
import Control.Monad.State
import SymbolTable
import System.FilePath
import AST

data Location = Reg String
              | MemLoc String
              | BaseOffset Int
              | GlobalOffset Int64 Int64

data LocInfo = LocInfo { symbolLocs :: Map.Map String Location 
                       , finalStackOffset :: Int }

-- Function to transform the intial HAST into an HAST with location information
createSymbolLocations :: Maybe (SymbolEnv LocInfo) -> SymbolEnv Int -> SymbolEnv LocInfo
createSymbolLocations (Just eParent) env = SymbolEnv { symbolBindings = symbolBindings env
                                                       , parentEnv = Just eParent
                                                       , customValue = locInfo }
    where methodCall = case (parentEnv eParent) of
                         Just _ -> False
                         Nothing -> True
          parentStackOffset = finalStackOffset $ customValue eParent 
          locInfo = LocInfo { symbolLocs = Map.fromList locs
                            , finalStackOffset = stackOffset } 
          (locs, stackOffset) = if methodCall 
                                then (methodArgLocations 0 (Map.keys $ symbolBindings env), 0)
                                else localSymbolLocations parentStackOffset (Map.keys $ symbolBindings env) 
createSymbolLocations Nothing env = SymbolEnv { symbolBindings = symbolBindings env
                                              , parentEnv = Nothing
                                              , customValue = locInfo }
    where locInfo = LocInfo { symbolLocs = Map.fromList locs
                            , finalStackOffset = 0 }
          locs = globalSymbolLocations 0 (Map.assocs $ symbolBindings env)

methodArgLocations :: Int -> [String] -> [(String, Location)]
methodArgLocations stackOffset [] = []
methodArgLocations stackOffset (x:xs) = (x, BaseOffset (stackOffset - 8)):(methodArgLocations (stackOffset-8) xs)

localSymbolLocations :: Int -> [String] -> ([(String, Location)], Int)
localSymbolLocations stackOffset [] = ([], stackOffset)
localSymbolLocations stackOffset (x:xs) = let (locs, returnStackOffset) = localSymbolLocations (stackOffset+8) xs
                                          in ((x, BaseOffset (stackOffset+8)):locs, returnStackOffset)


globalSymbolLocations :: Int64 -> [(String, SymbolTerm)] -> [(String, Location)]
globalSymbolLocations gOffset [] = []
globalSymbolLocations gOffset (x@(symbol, term):xs) = case term of 
                                                        MethodTerm _ _ -> globalSymbolLocations gOffset xs
                                                        Term _ _ -> (symbol, GlobalOffset gOffset (termSize term)):(globalSymbolLocations (gOffset+(termSize term)) xs)

createLocationInformation :: HDProgram Int -> HDProgram LocInfo
createLocationInformation program = transformHDProgram createSymbolLocations program

data CodeBlock = ConstantBlock [String] | CompoundBlock [CodeBlock]

instance Show CodeBlock where
    show (CompoundBlock blks) = unlines $ map show blks
    show (ConstantBlock instructions) = unlines instructions 

data CodeLabel = CodeLabel { lblName :: String, 
                             lblParent :: Maybe CodeLabel }

instance Show CodeLabel where
    show lbl@(CodeLabel { lblParent = Nothing }) = lblName lbl
    show lbl@(CodeLabel { lblParent = (Just prnt)}) = (show prnt) ++ "_" ++ (lblName lbl)

data CodeState = CodeState { globalOffset :: Int64,
                             globalStack :: [Int64],
                             localOffset :: Int64,
                             stringOffset :: Int64,
                             stringStack :: [String],
                             currentLabel :: CodeLabel } 

initialCodeState :: String -> CodeState
initialCodeState filename = CodeState { globalOffset = 0,
                                        globalStack = [],
                                        localOffset = 0,
                                        stringOffset = 0,
                                        stringStack = [],
                                        currentLabel = (CodeLabel {lblName=filename, lblParent=Nothing}) }

data BlockState = BlockState { numIfs :: Int
                             , numFors :: Int
                             , numWhiles :: Int }
initialBlockState :: BlockState
initialBlockState = BlockState { numIfs = 0
                               , numFors = 0
                               , numWhiles = 0 }

pushLoc :: Location -> CodeBlock 
pushLoc (Reg s) = ConstantBlock ["pushq %" ++ s]
pushLoc (MemLoc i) = ConstantBlock ["pushq " ++ (show i)]
pushLoc (BaseOffset i) = ConstantBlock ["pushq " ++ (show i) ++ "(%rbp)"]
pushLoc (GlobalOffset i s) = ConstantBlock ["pushq " ++ (show i) ++ "(GLOBALS)"]

methodToCode :: CodeState -> (HMethodDecl LocInfo) -> CodeBlock 
methodToCode codeState (HMethodDecl env _ _ tok args st) 
      = CompoundBlock [methodEntry, statementCode, methodExit]
    where methodLabel = CodeLabel { lblName = (tokenString tok), lblParent = Just $ currentLabel codeState}
          methodEntry = ConstantBlock [(show methodLabel) ++ ":", "# Perform method entry stuff"]
          methodExit = ConstantBlock ["# Perform method exit stuff"]
          statementCode = ConstantBlock ["# Perform Statements"]

--statementToCode :: BlockState -> CodeState -> (HStatement LocInfo) -> CodeBlock 
--statementToCode blockState codeState (HBlock env _ _ sts) 
  --  = CompoundBlock statementCodes
  -- where (_, statementCodes) = foldl  (blockState, []) sts

programToCode :: (HDProgram Int) -> State CodeState CodeBlock
programToCode program = do 
  let (HDProgram env _ _ methods) = createLocationInformation program
  codeState <- get
  put codeState { globalOffset = finalGlobalOffset env }
  codeState2@(CodeState {currentLabel=lbl}) <- get 
  -- Generate code for all of the methods
  let methodCode = CompoundBlock (map (methodToCode codeState2) methods)
  -- Generate a data area for the global variables in the program text
  let globalDecls = ConstantBlock [(show lbl) ++ "_GLOBALS: ", "# Allocate " ++ (show $ globalOffset codeState2) ++ " bytes of global memory here" ]
  return (CompoundBlock [methodCode, globalDecls])

finalGlobalOffset :: SymbolEnv LocInfo -> Int64 
finalGlobalOffset env =  case endLocations of 
                           [] -> 0
                           _ -> maximum endLocations
    where endLocations = map endLocation (Map.elems $ symbolLocs $ customValue env)
          endLocation (GlobalOffset loc size) = loc+size
          endLocation _ = 0

runGenerateCode :: (HDProgram Int) -> String -> CodeBlock
runGenerateCode program filedir = let (block, _) = runState (programToCode program)  (initialCodeState filename)
                                   in block
    where filename = takeBaseName filedir