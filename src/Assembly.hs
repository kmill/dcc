module Assembly where

import IR
import qualified Data.Map as Map
import Data.Graphs
import Text.ParserCombinators.Parsec.Pos

binOpInstr :: BinOp -> String
binOpInstr OpAdd = "addq"
binOpInstr OpSub = "subq"
binOpInstr OpMul = "imulq"
binOpInstr OpDiv = "idivq"
binOpInstr OpMod = "modq"
binOpInstr _ = ""

cmpBinOpString :: CmpBinOp -> String
cmpBinOpString CmpLT = "l"
cmpBinOpString CmpGT = "g"
cmpBinOpString CmpLTE = "le"
cmpBinOpString CmpGTE = "ge"
cmpBinOpString CmpEQ = "e"
cmpBinOpString CmpNEQ = "ne"

cmovInstr :: CmpBinOp -> String
cmovInstr cop = "cmov" ++ (cmpBinOpString cop) ++ "q"

jmpInstr :: CmpBinOp -> String
jmpInstr cop = "j" ++ (cmpBinOpString cop)

binInstr :: (Show a, Show b) => String -> a -> b -> String
binInstr cmd oper1 oper2 = cmd ++ " " ++ (show oper1) ++ ", " ++ (show oper2)

unInstr :: (Show a) => String -> a -> String
unInstr cmd oper = cmd ++ " " ++ (show oper)

--
-- Code for instructions inside basic blocks
-- 

instrCode :: LowIRInst -> [String]

instrCode (RegBin pos (X86Reg reg) (OpBinCmp cop) oper1 oper2) =
    [ binInstr "movq" (LowOperConst 0) reg
    , binInstr "movq" oper2 R10
    , binInstr "cmpq" oper1 R10
    , binInstr "movq" (LowOperConst 1) R10
    , binInstr (cmovInstr cop) R10 reg ]
      
instrCode (RegBin pos (X86Reg reg) op oper1 oper2) =
    [ binInstr "movq" oper2 reg ]
    ++ opS
    where opS = case op of
                     OpSub -> [ binInstr "movq" oper1 R10
                              , binInstr "subq" reg R10
                              , binInstr "movq" R10 reg ]
                     _ -> [binInstr (binOpInstr op) oper1 reg]

instrCode (RegUn pos (X86Reg reg) op oper) = 
    case op of
        OpNeg -> [ unInstr "neqg" reg ]
        OpNot -> [ unInstr "notq" reg ]
        _ -> error "shouldn't have derefs or addrs this low :-("

instrCode (RegVal pos (X86Reg reg) oper) =
    [ binInstr "movq" oper reg ]

instrCode (RegCond pos (X86Reg reg) cop oper1 oper2 src) =
    [ binInstr "movq" oper2 reg
    , binInstr "cmpq" oper1 reg
    , binInstr (cmovInstr cop) src reg ]

instrCode (RegPush pos oper) = [ unInstr "pushq" oper ]

instrCode (StoreMem pos addr oper) = [ binInstr "movq" oper addr ]

instrCode (LoadMem pos reg addr) = [ binInstr "movq" addr reg ]

instrCode (LowCall pos label _) = [ "call " ++ label ]

instrCode (LowCallout pos label nargs) = [ unInstr "pushq" RAX
                                         , binInstr "movq" (LowOperConst $ fromIntegral (nargs - 1)) RAX 
                                         , "call " ++ label
                                         , unInstr "popq" RAX ]

instrCode s = ["# Blargh! :-( Shouldn't have symbolic registers here: " ++ (show s)]

-- 
-- Code for block-ending tests
-- 

testCode :: String -> LowIRGraph -> Vertex -> [String]
testCode method (Graph graphMap _) vertex = 
    let (Just vPair) = Map.lookup vertex graphMap
        (BasicBlock _ test pos, edgeMap) = vPair
        trueEdge = case Map.lookup True edgeMap of
          Just x -> x
          Nothing -> 0
        falseEdge = case Map.lookup False edgeMap of
          Just x -> x
          Nothing -> 0
        trueLabel = vertexLabel method trueEdge
        falseLabel = vertexLabel method falseEdge
    in case test of
      IRTestTrue -> [ "jmp " ++ trueLabel ]
      IRTestFalse -> [ "jmp " ++ falseLabel ]
      IRTestBinOp cop oper1 oper2 ->
        [ binInstr "movq" oper2 R10
        , binInstr "cmpq" oper1 R10
        , (jmpInstr cop) ++ " " ++ trueLabel
        , "jmp " ++ falseLabel ]
      IRTest oper ->
        [ binInstr "cmpq" (LowOperConst 0) oper
        , "jnz " ++ trueLabel
        , "jmp " ++ falseLabel ]
      IRTestNot oper ->
        [ binInstr "cmpq" (LowOperConst 0) oper
        , "jz " ++ trueLabel
        , "jmp " ++ falseLabel ]
      IRReturn (Just oper) -> [ binInstr "movq" oper RAX 
                              , "jmp post_" ++ method ]
      IRReturn (Nothing) -> [ "jmp post_" ++ method ]
      IRTestFail _ ->
        [ binInstr "movq" (LowOperConst 1) RDI
        , "call exit" ]

--
-- Code for whole basic blocks
--

vertexLabel :: String -> Vertex -> String
vertexLabel method vertex = "block_" ++ method ++ "_" ++ (show vertex) ++ "_start"

basicBlockCode :: String -> LowIRGraph -> Vertex -> [String]
basicBlockCode method irGraph@(Graph graphMap _) vertex = [bLabel ++ ":"] ++ instrsCode ++ (testCode method irGraph vertex)
    where instrsCode = concatMap instrCode code
          (Just vPair) = Map.lookup vertex graphMap
          (bb@(BasicBlock code _ _), _) = vPair
          bLabel = vertexLabel method vertex

--
-- Translate method
--

calleeSaved :: [X86Reg]
calleeSaved = [ RBP, RBX, R12, R13, R14, R15 ]

methodCode :: LowIRMethod -> [String]
methodCode (LowIRMethod pos retP name numArgs localsSize irGraph) =
    [ name ++ ":"
    , "enter $(" ++ (show localsSize) ++ "), $0" ] ++
    map (unInstr "pushq") calleeSaved ++
    [ "jmp " ++ (vertexLabel name (startVertex irGraph))] ++
    concatMap (basicBlockCode name irGraph) (vertices irGraph) ++
    [ "post_" ++ name ++ ":"] ++
    map (unInstr "popq") (reverse calleeSaved) ++
    [ "leave"
    , "ret" ]

fieldsCode :: LowIRField -> [String]
fieldsCode (LowIRField _ name size) = [ name ++ ":"
                                      , "\t.long " ++ (show size)]
stringCode :: (String, SourcePos, String) -> [String]
stringCode (name, _, str) = [ name ++ ":"
                            , "\t.asciz " ++ (show $ str)]
--
-- Full translation
--

lowIRReprCode :: LowIRRepr -> [String]
lowIRReprCode (LowIRRepr fields strings methods) = [".section .data"]
    ++ concatMap fieldsCode fields
    ++ concatMap stringCode strings
    ++ [".globl main"]
    ++ concatMap methodCode methods
--    ++ methodCode (head $ filter (\x -> ("main" == lowIRMethodName x)) methods)
