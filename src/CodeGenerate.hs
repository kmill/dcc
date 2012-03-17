module CodeGenerate where

import qualified Data.Map as Map 
import qualified Data.List as List
import Data.Char
import Data.Int
import Control.Monad.State
import SymbolTable
import System.FilePath
import AST

data Location = Reg String
              | MemLoc String
              | BaseOffset Int
              | GlobalOffset Int64 Int64

instance Show Location where
    show (Reg s) = "%" ++ s
    show (MemLoc s) = s
    show (BaseOffset i) = (show i) ++ "(%rbp)"
    show (GlobalOffset i _) = (show i)
                                                 
data LocInfo = LocInfo { symbolLocs :: Map.Map String Location 
                       , finalStackOffset :: Int }

lookupLocInfo :: String -> SymbolEnv LocInfo ->  Maybe Location
lookupLocInfo name env = Map.lookup name locations 
                         `mplus` ((parentEnv env) >>= lookupLocInfo name)
    where locations = symbolLocs $ customValue env

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
unlinesWithoutEnd = List.intercalate "\n"

data CodeLabel = CodeLabel { lblName :: String, 
                             lblParent :: Maybe CodeLabel }

instance Show CodeLabel where
    show lbl@(CodeLabel { lblParent = Nothing }) = lblName lbl
    show lbl@(CodeLabel { lblParent = (Just prnt)}) = (show prnt) ++ "_" ++ (lblName lbl)


data CodeState = CodeState { currentLabel :: CodeLabel
                           , currentIfIndex :: Int
                           , currentForIndex :: Int
                           , currentWhileIndex :: Int 
                           , currentOrIndex :: Int 
                           , currentAndIndex :: Int 
                           , stringLiterals :: [String]
                           , currentStringOffset :: Int}
                           

initialCodeState :: String -> CodeState
initialCodeState filename = CodeState { currentLabel = (CodeLabel {lblName=filename, lblParent=Nothing})
                                      , currentIfIndex = 0
                                      , currentForIndex = 0
                                      , currentWhileIndex = 0
                                      , currentOrIndex = 0
                                      , currentAndIndex = 0 
                                      , stringLiterals = []
                                      , currentStringOffset = 0}

subBlockState :: CodeState -> CodeState
subBlockState codeState = codeState { currentIfIndex = 0
                                    , currentForIndex = 0
                                    , currentWhileIndex = 0
                                    , currentOrIndex = 0
                                    , currentAndIndex = 0 } 

updateState :: CodeState -> CodeState -> CodeState
updateState codeState subState = codeState { stringLiterals = stringLiterals subState
                                           , currentStringOffset = currentStringOffset subState }

-- | BlockStates contain data that is maintained as state while a single block of code is being evaluated. 
-- | Their primary purpose is to allow for universal labels to be generated
data BlockState = BlockState { numIfs :: Int
                             , numFors :: Int
                             , numWhiles :: Int
                             , numOrs :: Int 
                             , numAnds :: Int
                             , stringTable :: [String]
                             , stringOffset :: Int}
initialBlockState :: BlockState
initialBlockState = BlockState { numIfs = 0
                               , numFors = 0
                               , numWhiles = 0 
                               , numOrs = 0
                               , numAnds = 0
                               , stringTable = []
                               , stringOffset = 0 }

pushLoc :: Location -> CodeBlock 
pushLoc (Reg s) = ConstantBlock ["pushq %" ++ s]
pushLoc (MemLoc i) = ConstantBlock ["pushq " ++ (show i)]
pushLoc (BaseOffset i) = ConstantBlock ["pushq " ++ (show i) ++ "(%rbp)"]
pushLoc (GlobalOffset i s) = ConstantBlock ["pushq " ++ (show i) ++ "(GLOBALS)"]

moveLoc :: Location -> Location -> CodeBlock 
moveLoc loc1 loc2 = stringBlock $ "movq " ++ (show loc1) ++ ", " ++ (show loc2)


hdLocToLoc :: (HDLocation LocInfo) -> Location 
hdLocToLoc (HPlainLocation env _ tok) = let name = tokenString tok 
                                        in case (lookupLocInfo name env) of 
                                          Just loc -> loc
                                          Nothing -> error "Attempted to lookup name that doesn't exist"
hdLocToLoc (HArrayLocation env _ tok  _) = let name = tokenString tok 
                                           in case (lookupLocInfo name env) of 
                                             Just loc -> loc 
                                             Nothing -> error "Attempted to lookup name that doesn't exist"

stringDataBlock :: String -> CodeBlock 
stringDataBlock str = ConstantBlock [".string \"" ++ str ++ "\""]

labelBlock :: CodeLabel -> CodeBlock 
labelBlock label = ConstantBlock [(show label)++":"]

stringBlock :: String -> CodeBlock
stringBlock str = ConstantBlock [str]

--- 
--- 
---

{- Testing out the State monad replacement for the old code -}
methodToCode :: (HMethodDecl LocInfo) -> State CodeState CodeBlock 
methodToCode (HMethodDecl env _ _ tok args st) 
    = do codeState <- get
         let codeBlock = CompoundBlock [ stringBlock ""
                                       , methodEntry
                                       , statementCode 
                                       , methodExit
                                       , stringBlock "" ]
             methodLabel = CodeLabel { lblName = (tokenString tok), lblParent = Just $ currentLabel codeState }
             methodEntry = CompoundBlock [ labelBlock methodLabel, stringBlock "# Perform method entry stuff"]
             methodExit = CompoundBlock [ stringBlock "# Perform method exit stuff"]
             subState = codeState { currentLabel = methodLabel }
             (statementCode, statementState) = runState (statementToCode st) subState
             newState = statementState { currentLabel = currentLabel codeState }
         put newState 
         return codeBlock 
   
---
--- Generate code for statements 
---          


statementToCode :: HStatement LocInfo -> State CodeState CodeBlock
statementToCode (HBlock env _ _ sts) 
    = do childCodes <- stateMap statementToCode sts
         return $ CompoundBlock childCodes 

-- | Convert If Statements to a code block 
statementToCode (HIfSt env _ expr st maybeelse) 
    = do codeState <- get 
         let ifIndex = currentIfIndex codeState
             ifLabel = CodeLabel { lblName = "if_" ++ (show ifIndex), lblParent = Just (currentLabel codeState) }
             ifTrueLabel = CodeLabel { lblName = "true", lblParent = Just ifLabel }
             ifFalseLabel = CodeLabel { lblName = "false", lblParent = Just ifLabel }
             ifEndLabel = CodeLabel { lblName = "end", lblParent = Just ifLabel }
             codeBlock = CompoundBlock [ labelBlock ifLabel
                                       , evalExprCode
                                       , labelBlock ifTrueLabel
                                       , trueCode
                                       , stringBlock $ "jmp " ++ (show ifEndLabel)
                                       , labelBlock ifFalseLabel
                                       , falseCode
                                       , labelBlock ifEndLabel ]
             evalExprCode = CompoundBlock [ stringBlock "# Eval if Expr here"
                                          , exprCode
                                          , stringBlock "popq %rax"
                                          , stringBlock "cmp 1, %rax"
                                          , stringBlock ("jne " ++ (show ifFalseLabel))]
             subState = (subBlockState codeState) { currentLabel = ifLabel }
             (exprCode, exprState) = runState (exprToCode expr) subState
             trueCode = CompoundBlock [stringBlock "# Perform if true", trueCodes]
             (trueCodes, trueState) = runState (statementToCode st) exprState
             falseCode = CompoundBlock [stringBlock "# Perform if false", falseCodes]
             (falseCodes, falseState) = case maybeelse of 
                                        Just stelse -> runState (statementToCode st) (subBlockState trueState)
                                        Nothing -> (CompoundBlock [], trueState)
             newState = (updateState codeState falseState) { currentIfIndex = ifIndex + 1 }
         put newState
         return codeBlock

-- | Convert For loops to a code block 
statementToCode (HForSt env _ _ expr1 expr2 st)
    = do codeState <- get 
         let forIndex = currentForIndex codeState
             forLabel = CodeLabel { lblName = "for_" ++ (show forIndex), lblParent = Just (currentLabel codeState) }
             forEvalLabel = CodeLabel { lblName = "eval", lblParent = Just forLabel}
             forReloopLabel = CodeLabel { lblName = "reloop", lblParent = Just forLabel}
             forEndLabel = CodeLabel {lblName = "end", lblParent = Just forLabel}
             subState = (subBlockState codeState) { currentLabel = forLabel }
             codeBlock = CompoundBlock [ labelBlock forLabel
                                    , initCode
                                    , labelBlock forEvalLabel
                                    , evalExprCode
                                    , loopStCode
                                    , labelBlock forReloopLabel
                                    , postLoopCode
                                    , labelBlock forEndLabel]
             initCode = CompoundBlock [ stringBlock "# init looping variable here"
                                      , iECode
                                      , putTokBlock]
             (iECode, iEState) = runState (exprToCode expr1) subState
             evalExprCode = CompoundBlock [ stringBlock "# Eval the for expr here"
                                          , eECode
                                          , stringBlock "popq %rax"
                                          , getTokBlock
                                          , stringBlock "popq %rbx"
                                          , stringBlock "cmp %rax, %rbx"
                                          , stringBlock ("jge " ++ (show forEndLabel))] 
             (eECode, eEState) = runState (exprToCode expr2) iEState 
             loopStCode = CompoundBlock [stringBlock "# Inner loop code here", loopCodes]
             (loopCodes, loopState) = runState (statementToCode st) eEState
             postLoopCode = CompoundBlock [ stringBlock "# Increment loop variable and re-loop here"
                                          , getTokBlock
                                          , stringBlock "popq %rax"
                                          , stringBlock "addc 1, %rax"
                                          , stringBlock "pushq %rax"
                                          , putTokBlock]
             getTokBlock = stringBlock "#Get Value from Tok and put on stack"
             putTokBlock = stringBlock "#Put Value from Stack and put in Tok"
             newState = (updateState codeState loopState) { currentForIndex = forIndex+1 } 
         put newState 
         return codeBlock 

-- | Convert While loops to a code block
statementToCode (HWhileSt env _ expr st) 
    = do codeState <- get 
         let whileIndex = currentWhileIndex codeState
             whileLabel = CodeLabel { lblName = "while_" ++ (show whileIndex), lblParent = Just (currentLabel codeState) } 
             whileEvalLabel = CodeLabel { lblName = "eval", lblParent = Just whileLabel }
             whileReloopLabel = CodeLabel { lblName = "reloop", lblParent = Just whileLabel }
             whileEndLabel = CodeLabel { lblName = "end", lblParent = Just whileLabel }
             subState = (subBlockState codeState) { currentLabel = whileLabel } 
             codeBlock = CompoundBlock [ labelBlock whileLabel
                                       , labelBlock whileEvalLabel
                                       , evalExprCode
                                       , loopStCode
                                       , labelBlock  whileReloopLabel
                                       , postLoopCode
                                       , labelBlock whileEndLabel]
             evalExprCode = CompoundBlock [ stringBlock "# Eval the expr" 
                                          , eCode
                                          , stringBlock "popq %rax"
                                          , stringBlock "cmp 1, %rax"
                                          , stringBlock $ "jne " ++ (show whileEndLabel)] 
             (eCode, eState) = runState (exprToCode expr) subState
             loopStCode = CompoundBlock [stringBlock "# inner loop code here", loopCodes]
             (loopCodes, loopState) = runState (statementToCode st) eState
             postLoopCode = stringBlock $ "jmp " ++ (show whileEvalLabel)
             newState = (updateState codeState loopState) { currentWhileIndex = whileIndex + 1 }
         put newState 
         return codeBlock 

-- | Convert Return statements to a code block
statementToCode (HReturnSt env _ maybeExpr) 
    = do codeState <- get
         let codeBlock = CompoundBlock [ evalExprCode
                                       , returnCode]
             evalExprCode = stringBlock "# Eval the return expr here" 
             returnCode = stringBlock "# Return from the method here"
             newState = codeState
         put newState 
         return codeBlock 

-- | Convert Break statements to a code block 
statementToCode (HBreakSt env _) 
    = do codeState <- get 
         let codeBlock = CompoundBlock [ breakCode ]
             endLabel = CodeLabel { lblName = "end", lblParent = Just (currentLabel codeState) }
             breakCode = stringBlock $ "jmp " ++ (show endLabel)
         return codeBlock 
          
-- | Convert Continue statements to a code block 
statementToCode (HContinueSt env _) 
    = do codeState <- get 
         let codeBlock = CompoundBlock [ continueCode ]
             reloopLabel = CodeLabel { lblName = "reloop", lblParent = Just (currentLabel codeState) }
             continueCode = stringBlock $ "jmp " ++ (show reloopLabel)          
         return codeBlock 

-- | Convert Expr statements to a code block 
statementToCode (HExprSt env expr)
    = do codeState <- get 
         let codeBlock = CompoundBlock [ evalExprCode
                                    , discardResultCode ]
             evalExprCode = stringBlock "# Eval an expr here"
             discardResultCode = stringBlock "popq %rax"   
             newState = codeState
         put newState 
         return codeBlock 

-- | Convert an Assign Statement to a code block 
statementToCode (HAssignSt env _ loc op expr)
    = do codeState <- get 
         let codeBlock = CompoundBlock [ evalExprCode
                                       , moveResultCode ] 
             evalExprCode = stringBlock "# Eval assignment expr here" 
             moveResultCode = stringBlock "# Move result into location here"
             newState = codeState
         put newState 
         return codeBlock 
   

---
--- Generate code for expressions 
---


exprToCode :: (HExpr LocInfo) -> State CodeState CodeBlock 
exprToCode (HBinaryOp env _ expr1 tok expr2) 
    = binOpExprToCode expr1 expr2 (tokenString tok) 
exprToCode (HUnaryOp env _ tok expr) 
    = unaryOpExprToCode expr (tokenString tok) 
exprToCode (HExprBoolLiteral _ _ value) 
    = boolToBlock value
exprToCode (HExprIntLiteral _ _ value)
    = intToBlock value
exprToCode (HExprCharLiteral _ _ value)
    = charToBlock value
exprToCode (HExprStringLiteral _ _ value) 
    = return $ stringBlock "TODO: figure out string literals"
exprToCode (HLoadLoc env _ loc) 
    = return $ pushLoc $ hdLocToLoc $ loc
exprToCode (HExprMethod env _ method) 
    = methodCallToCode method


---
--- Method calls
---
methodCallToCode :: HMethodCall LocInfo -> State CodeState CodeBlock 
methodCallToCode (HNormalMethod env _ tok args)
    = do codeState <-  get 
         let codeBlock = CompoundBlock [preCallCode, callCode, postCallCode]
             preCallCode = stringBlock "# TODO: implement expr evaluation"
             callCode = stringBlock $ "jmp " ++ (show tok)
             postCallCode = stringBlock "# TODO: implement post-call code"
             newState = codeState
         put newState 
         return codeBlock 

methodCallToCode (HCalloutMethod env _ tok args)  
    = return $ stringBlock "# TODO: Implement Call-outs" 

---
--- Literals
---

boolToBlock :: Bool -> State CodeState CodeBlock
boolToBlock value 
    = return $ CompoundBlock [ stringBlock instr ]
      where instr = case value of
                      False -> "pushq 0x00"
                      True -> "pushq 0x01"

intToBlock :: Int64 -> State CodeState CodeBlock
intToBlock value 
    = return $ CompoundBlock [ stringBlock $ "pushq " ++ show value ]

charToBlock :: Char -> State CodeState CodeBlock
charToBlock value 
    = return $ CompoundBlock [ stringBlock instr ]
    where instr = "pushq " ++ (show $ ord value)

--- 
--- Unary operations code 
--- 

unaryOpExprToCode :: HExpr LocInfo -> String -> State CodeState CodeBlock
unaryOpExprToCode expr opStr
    = let f = case opStr of
                "!" -> notExprToCode
                "-" -> negExprToCode
                s   -> error $ "Unexpected token \"" ++ s ++ "\" for unary operator"
      in f expr 

notExprToCode :: HExpr LocInfo -> State CodeState CodeBlock  
notExprToCode expr 
    = do codeState <- get 
         let (exprBlock, exprBlockState) = runState (exprToCode expr) codeState                             
             codeBlock = CompoundBlock [ exprBlock
                                       , stringBlock "popq %rax" 
                                       , stringBlock "xorq 0x01, %rax" -- will only xor booleans
                                       , stringBlock "pushq %rax" ]
             newState = exprBlockState 
         put newState 
         return codeBlock

negExprToCode :: HExpr LocInfo -> State CodeState CodeBlock 
negExprToCode expr  
    = do codeState <- get 
         let (exprBlock, exprBlockState) = runState (exprToCode expr) codeState
             codeBlock = CompoundBlock [ exprBlock
                                       , stringBlock "popq %rax" 
                                       , stringBlock "negq %rax"
                                       , stringBlock "pushq %rax" ]
             newState = exprBlockState 
         put newState
         return codeBlock 

 
---
--- Binary operations code 
--- 
binOpExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> String -> State CodeState CodeBlock
binOpExprToCode exprLeft exprRight opStr
    = let f = case opStr of 
                "||" -> orExprToCode 
                "&&" -> andExprToCode 
                "+" -> addExprToCode 
                "-" -> subExprToCode 
                "*" -> mulExprToCode 
                "/" -> divExprToCode  
                "%" -> modExprToCode
                "==" -> equalsExprToCode
                "!=" -> notEqualsExprToCode
                "<" -> ltExprToCode
                ">" -> gtExprToCode
                "<=" -> ltEqualsExprToCode 
                ">=" -> gtEqualsExprToCode 
                _ -> error "Unexpected token for operator" 
      in f exprLeft exprRight

addExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
addExprToCode leftExpr rightExpr
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax" 
                                       , stringBlock "popq %rbx"
                                       , stringBlock "addq %rax, %rbx" 
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

subExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
subExprToCode leftExpr rightExpr  
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax" 
                                       , stringBlock "popq %rbx"
                                       , stringBlock "subq %rax, %rbx" 
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

mulExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
mulExprToCode leftExpr rightExpr
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax" 
                                       , stringBlock "popq %rbx"
                                       , stringBlock "mulq %rax, %rbx" 
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

divExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
divExprToCode leftExpr rightExpr
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax" 
                                       , stringBlock "popq %rbx"
                                       , stringBlock "divq %rax, %rbx" 
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

modExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
modExprToCode leftExpr rightExpr
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax" 
                                       , stringBlock "popq %rbx"
                                       , stringBlock "modq %rax, %rbx" 
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

equalsExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
equalsExprToCode leftExpr rightExpr 
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax"
                                       , stringBlock "popq %rbx" 
                                       , stringBlock "cmpq %rax, %rbx"
                                       , stringBlock "pushfq"
                                       , stringBlock "popq %rax"
                                       , stringBlock "andq 0x40, %rax" 
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

notEqualsExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
notEqualsExprToCode leftExpr rightExpr
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax"
                                       , stringBlock "popq %rbx" 
                                       , stringBlock "cmpq %rax, %rbx"
                                       , stringBlock "pushfq"
                                       , stringBlock "popq %rax"
                                       , stringBlock "andq 0x40, %rax"
                                       , stringBlock "xorq 0x40, %rax"
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

ltExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
ltExprToCode leftExpr rightExpr
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax"
                                       , stringBlock "popq %rbx" 
                                       , stringBlock "cmpq %rax, %rbx"
                                       , stringBlock "pushfq"
                                       , stringBlock "popq %rax"
                                       , stringBlock "andq 0x80, %rax"
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

gtExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
gtExprToCode leftExpr rightExpr
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax"
                                       , stringBlock "popq %rbx" 
                                       , stringBlock "cmpq %rbx, %rax"
                                       , stringBlock "pushfq"
                                       , stringBlock "popq %rax"
                                       , stringBlock "andq 0x80, %rax"
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

ltEqualsExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
ltEqualsExprToCode leftExpr rightExpr
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax"
                                       , stringBlock "popq %rbx" 
                                       , stringBlock "cmpq %rax, %rbx"
                                       , stringBlock "pushfq"
                                       , stringBlock "popq %rax"
                                       , stringBlock "andq 0xC0, %rax"
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

gtEqualsExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock  
gtEqualsExprToCode leftExpr rightExpr
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             codeBlock = CompoundBlock [ leftBlock 
                                       , rightBlock 
                                       , stringBlock "popq %rax"
                                       , stringBlock "popq %rbx" 
                                       , stringBlock "cmpq %rbx, %rax"
                                       , stringBlock "pushfq"
                                       , stringBlock "popq %rax"
                                       , stringBlock "andq 0xC0, %rax"
                                       , stringBlock "pushq %rax" ]
             newState = rightBlockState
         put newState
         return codeBlock 

orExprToCode ::  (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock 
orExprToCode leftExpr rightExpr  
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState  
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             orIndex = currentOrIndex rightBlockState
             orLabel = CodeLabel { lblName = "or_" ++ (show orIndex), lblParent = Just $ currentLabel codeState }
             orTrueLabel = CodeLabel { lblName = "true", lblParent = Just orLabel }
             orEndLabel = CodeLabel { lblName = "end", lblParent = Just orLabel }
             codeBlock = CompoundBlock [ leftBlock 
                                       , stringBlock "popq %rax"
                                       , stringBlock "cmp %rax, $0"
                                       , stringBlock $ "jne " ++ (show orTrueLabel)
                                       , rightBlock
                                       , stringBlock "popq %rax"
                                       , stringBlock "cmp %rax, $0"
                                       , stringBlock $ "jne " ++ (show orTrueLabel)
                                       , stringBlock "pushq $0"
                                       , stringBlock $ "jmp " ++ (show orEndLabel)
                                       , labelBlock orTrueLabel
                                       , stringBlock "pushq $1"
                                       , labelBlock orEndLabel]
             newState = rightBlockState { currentOrIndex = orIndex + 1 }
         put newState 
         return codeBlock

andExprToCode :: (HExpr LocInfo) -> (HExpr LocInfo) -> State CodeState CodeBlock 
andExprToCode leftExpr rightExpr 
    = do codeState <- get 
         let (leftBlock, leftBlockState) = runState (exprToCode leftExpr) codeState
             (rightBlock, rightBlockState) = runState (exprToCode rightExpr) leftBlockState
             andIndex = currentAndIndex rightBlockState
             andLabel = CodeLabel { lblName = "and_" ++ (show andIndex), lblParent = Just $ currentLabel codeState }
             andFalseLabel = CodeLabel { lblName = "false", lblParent = Just andLabel }
             andEndLabel = CodeLabel { lblName = "end", lblParent = Just andLabel }
             codeBlock = CompoundBlock [ leftBlock 
                                       , stringBlock "popq %rax" 
                                       , stringBlock "cmp %rax, $0"
                                       , stringBlock $ "je " ++ (show andFalseLabel) 
                                       , rightBlock
                                       , stringBlock "popq %rax"
                                       , stringBlock "cmp %rax, $0"
                                       , stringBlock $ "je " ++ (show andFalseLabel) 
                                       , stringBlock "pushq $1" 
                                       , stringBlock $ "jmp " ++ (show andEndLabel)
                                       , labelBlock andFalseLabel
                                       , stringBlock "pushq $0"
                                       , labelBlock andEndLabel ]
             newState = rightBlockState { currentAndIndex = andIndex + 1 }
         put newState 
         return codeBlock 

---
--- Code generation for the entire program. 
---

programToCode :: (HDProgram Int) -> State CodeState CodeBlock
programToCode program = do 
  let (HDProgram env _ _ methods) = createLocationInformation program
      fullGlobalOffset = finalGlobalOffset env
  -- Generate code for all of the methods
  methodCode <- stateMap methodToCode methods
  --let methodCode = CompoundBlock (map (methodToCode codeState) methods)
  -- Generate a data area for the global variables in the program text
  let globalDecls = ConstantBlock ["GLOBALS:", "# Allocate " ++ (show $ fullGlobalOffset) ++ " bytes of global memory here" ]
  return (CompoundBlock [CompoundBlock methodCode, globalDecls])

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


stateMap :: (a -> State s b) -> [a] -> State s [b] 
stateMap f [] = return []
stateMap f (x:xs) = do y <- f x 
                       ys <- stateMap f xs 
                       return (y:ys)

