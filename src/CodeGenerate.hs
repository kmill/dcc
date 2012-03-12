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
    show (CompoundBlock blks) = unlinesWithoutEnd $ map show blks
    show (ConstantBlock instructions) = unlinesWithoutEnd instructions 

-- Simple function that does the same thing as unlines without including a newLine after the final element
unlinesWithoutEnd :: [String] -> String
unlinesWithoutEnd  [] = []
unlinesWithoutEnd  (x:[]) = x
unlinesWithoutEnd  (x:xs) = x ++ "\n" ++ (unlinesWithoutEnd xs)


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

labelBlock :: CodeLabel -> CodeBlock 
labelBlock label = ConstantBlock [(show label)++":"]

stringBlock :: String -> CodeBlock
stringBlock str = ConstantBlock [str]

methodToCode :: CodeState -> (HMethodDecl LocInfo) -> CodeBlock 
methodToCode codeState (HMethodDecl env _ _ tok args st) 
      = CompoundBlock [stringBlock "", methodEntry, statementCode, methodExit, stringBlock ""]
    where methodLabel = CodeLabel { lblName = (tokenString tok), lblParent = Just $ currentLabel codeState}
          methodEntry = ConstantBlock [(show methodLabel) ++ ":", "# Perform method entry stuff"]
          methodExit = ConstantBlock ["# Perform method exit stuff"]
          statementCode = CompoundBlock statementCodes 
          (_, statementCodes) = statementToCode (codeState { currentLabel = methodLabel}) st (initialBlockState, [])

statementToCode :: CodeState -> (HStatement LocInfo) -> (BlockState, [CodeBlock]) -> (BlockState, [CodeBlock]) 
statementToCode codeState (HBlock env _ _ sts) (blockState, codeBlocks) 
    = (blockState, [CompoundBlock childCodes])
    where (_, childCodes) = foldr (statementToCode codeState) (blockState, codeBlocks) sts

-- | Convert If Statements to a code block
statementToCode codeState (HIfSt env _ expr st maybeelse) (blockState, codeBlocks) 
    = (blockState { numIfs = ifIndex+1 }, codeBlock:codeBlocks)
    where ifIndex = numIfs blockState
          ifLabel = CodeLabel { lblName = "if_" ++ (show ifIndex), lblParent = Just (currentLabel codeState) }
          ifTrueLabel = CodeLabel { lblName = "true", lblParent = Just ifLabel }
          ifFalseLabel = CodeLabel { lblName = "false", lblParent = Just ifLabel }
          ifEndLabel = CodeLabel { lblName = "end", lblParent = Just ifLabel }
          codeBlock = CompoundBlock [labelBlock ifLabel
                                    , evalExprCode
                                    , labelBlock ifTrueLabel
                                    , trueCode
                                    , labelBlock ifFalseLabel
                                    , falseCode
                                    , labelBlock ifEndLabel]
          evalExprCode = stringBlock "# Eval if Expr here"
          trueCode = CompoundBlock [stringBlock "# Perform if true", CompoundBlock trueCodes]
          (_, trueCodes) = statementToCode codeState st (initialBlockState, [])
          falseCode = case maybeelse of 
                        Just stelse -> let (_, falseCodes) = statementToCode codeState stelse (initialBlockState, [])
                                       in CompoundBlock [stringBlock "# Perform Otherwise", CompoundBlock falseCodes]
                        Nothing -> CompoundBlock []

-- | Convert For loops to a code block 
statementToCode codeState (HForSt env _ _ expr1 expr2 st) (blockState, codeBlocks)
    = (blockState {numFors = forIndex+1}, codeBlock:codeBlocks)
    where forIndex = numFors blockState
          forLabel = CodeLabel { lblName = "for_" ++ (show forIndex), lblParent = Just (currentLabel codeState) }
          forEvalLabel = CodeLabel { lblName = "eval", lblParent = Just forLabel}
          forReloopLabel = CodeLabel { lblName = "reloop", lblParent = Just forLabel}
          forEndLabel = CodeLabel {lblName = "end", lblParent = Just forLabel}
          newState = codeState { currentLabel = forLabel}
          codeBlock = CompoundBlock [ labelBlock forLabel
                                    , initCode
                                    , labelBlock forEvalLabel
                                    , evalExprCode
                                    , loopStCode
                                    , labelBlock forReloopLabel
                                    , postLoopCode
                                    , labelBlock forEndLabel]
          initCode = stringBlock "# init looping variable here"
          evalExprCode = stringBlock "# Eval the for expr here" 
          loopStCode = CompoundBlock [stringBlock "# Inner loop code here", CompoundBlock loopCodes]
          (_, loopCodes) = statementToCode newState st (initialBlockState, [])
          postLoopCode = stringBlock "# Increment loop variable and re-loop here"

-- | Convert While loops to a code block
statementToCode codeState (HWhileSt env _ expr st) (blockState, codeBlocks) 
    = (blockState {numWhiles = whileIndex+1}, codeBlock:codeBlocks)
    where whileIndex = numWhiles blockState
          whileLabel = CodeLabel { lblName = "while_" ++ (show whileIndex), lblParent = Just (currentLabel codeState) } 
          whileEvalLabel = CodeLabel { lblName = "eval", lblParent = Just whileLabel }
          whileReloopLabel = CodeLabel { lblName = "reloop", lblParent = Just whileLabel }
          whileEndLabel = CodeLabel { lblName = "end", lblParent = Just whileLabel }
          newState = codeState { currentLabel = whileLabel }
          codeBlock = CompoundBlock [ labelBlock whileLabel
                                    , labelBlock whileEvalLabel
                                    , evalExprCode
                                    , loopStCode
                                    , labelBlock  whileReloopLabel
                                    , postLoopCode
                                    , labelBlock whileEndLabel]
          evalExprCode = stringBlock "# Eval the while expr here" 
          loopStCode = CompoundBlock [stringBlock "# inner loop code here", CompoundBlock loopCodes]
          (_, loopCodes) = statementToCode newState st (initialBlockState, [])
          postLoopCode = stringBlock $ "jmp " ++ (show whileEvalLabel)

-- | Convert Return statements to a code block
statementToCode codeState (HReturnSt env _ maybeExpr) (blockState, codeBlocks)
    = (blockState, codeBlock:codeBlocks)
    where codeBlock = CompoundBlock [ evalExprCode
                                    , returnCode ]
          evalExprCode = stringBlock "# Eval the return expr here" 
          returnCode = stringBlock "# Return from the method here"

-- | Convert Break statements to a code block 
statementToCode codeState (HBreakSt env _) (blockState, codeBlocks) 
    = (blockState, codeBlock:codeBlocks)
    where codeBlock = CompoundBlock [ breakCode ]
          endLabel = CodeLabel { lblName = "end", lblParent = Just (currentLabel codeState) }
          breakCode = stringBlock $ "jmp " ++ (show endLabel)

-- | Convert Continue statements to a code block 
statementToCode codeState (HContinueSt env _) (blockState, codeBlocks) 
    = (blockState, codeBlock:codeBlocks) 
    where codeBlock = CompoundBlock [ continueCode ]
          reloopLabel = CodeLabel { lblName = "reloop", lblParent = Just (currentLabel codeState) }
          continueCode = stringBlock $ "jmp " ++ (show reloopLabel)

-- | Convert Expr statements to a code block 
statementToCode codeState (HExprSt env expr) (blockState, codeBlocks)
    = (blockState, codeBlock:codeBlocks) 
    where codeBlock = CompoundBlock [ evalExprCode
                                    , discardResultCode ]
          evalExprCode = stringBlock "# Eval an expr here"
          discardResultCode = stringBlock "popq %rax"

-- | Convert an Assign Statement to a code block 
statementToCode codeState (HAssignSt env _ loc op expr) (blockState, codeBlocks)
    = (blockState, codeBlock:codeBlocks)
    where codeBlock = CompoundBlock [ evalExprCode
                                    , moveResultCode]
          evalExprCode = stringBlock "# Eval assignment expr here"
          moveResultCode = stringBlock "# Move result into location here" 



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