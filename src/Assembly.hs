module Assembly where

import IR
import qualified Data.Map as Map
import Control.Applicative
import Data.Graphs

binOpInstr :: BinOp -> String
binOpInstr OpAdd = "addq"
binOpInstr OpSub = "subq"
binOpInstr OpMul = "mulq"
binOpInstr OpDiv = "divq"
binOpInstr OpMod = "modq"
binOpInstr _ = ""

cmovInstr :: CmpBinOp -> String
cmovInstr CmpLT = "cmovlq"
cmovInstr CmpGT = "cmovgq"
cmovInstr CmpLTE = "cmovleq"
cmovInstr CmpGTE = "cmovgeq"
cmovInstr CmpEQ = "cmoveq"
cmovInstr CmpNEQ = "cmovneq"

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
    , binInstr "cmpq" oper1 oper2
    , binInstr (cmovInstr cop) (LowOperConst 1) reg ]
      
instrCode (RegBin pos (X86Reg reg) op oper1 oper2) =
    [ binInstr "movq" oper2 reg
    , binInstr opS oper1 reg ]
    where opS = binOpInstr op

instrCode (RegUn pos (X86Reg reg) op oper) = 
    case op of
        OpNeg -> [ unInstr "neqg" reg ]
        OpNot -> [ unInstr "notq" reg ]
        _ -> error "shouldn't have derefs or addrs this low :-("

instrCode (RegVal pos (X86Reg reg) oper) =
    [ binInstr "movq" oper reg ]

instrCode (RegCond pos (X86Reg reg) cop oper1 oper2 src) =
    [ binInstr "cmpq" oper1 oper2
    , binInstr (cmovInstr cop) src reg ]

instrCode (RegPush pos oper) = [ unInstr "pushq" oper ]

instrCode (StoreMem pos addr oper) = [ binInstr "movq" oper addr ]

instrCode (LoadMem pos reg addr) = [ binInstr "movq" addr reg ]

instrCode (LowCall pos label _) = [ "call " ++ label ]

instrCode (LowCallout pos label _) = [ "call " ++ label ]

instrCode s = ["#Not Implemented: " ++ (show s)]
-- 
-- Code for block-ending tests
-- 

testCode :: (LowBasicBlock, Map.Map Bool Vertex) -> [String]
testCode ((BasicBlock code test pos), edgeMap) =
    [ "# TODO: Implement basic block tests" ]

--
-- Code for whole basic blocks
--

basicBlockCode :: LowIRGraph -> Vertex -> [String]
basicBlockCode (Graph graphMap _) vertex = instrsCode ++ (testCode vPair)
    where instrsCode = concatMap instrCode code
          (Just vPair) = Map.lookup vertex graphMap
          (BasicBlock code _ _, _) = vPair

--
-- Translate method
--

methodCode :: LowIRMethod -> [String]
methodCode (LowIRMethod pos retP name numArgs localsSize irGraph) =
  [ name ++ ":"
  , "#TODO: Implement arguments" ]
  ++ concatMap (basicBlockCode irGraph) [ vertices irGraph]
  ++ ["ret"]

fieldsCode :: LowIRField -> [String]
fieldsCode (LowIRField _ name size) = [ name ++ ":"
                                      , "\t.long " ++ (show size)]

stringCode (name, _, str) = [ name ++ ":"
                              , "\t.ascii " ++ (show str)]
--
-- Full translation
--

lowIRReprCode :: LowIRRepr -> [String]
lowIRReprCode (LowIRRepr fields strings methods) = [".section .data"]
  ++ concatMap fieldsCode fields
  ++ concatMap stringCode strings
  ++ [".glbl main"]
  ++ concatMap methodCode methods  
