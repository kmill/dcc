module Assembly where

import IR

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

-- 
-- Code for block-ending tests
-- 

testCode :: IRTest LowOper -> [String]
testCode _ = [ "# TODO: Implement basic block tests" ]

--
-- Code for whole basic blocks
--

basicBlockCode :: LowBasicBlock -> [String]
basicBlockCode (BasicBlock code test testPos) = instrsCode ++ (testCode test)
    where instrsCode = concat $ map instrCode code

--
-- Translate method
--

methodCode :: LowIRMethod -> [String]
methodCode (LowIRMethod pos retP name numArgs localsSize irGraph) =
    [ "# TODO: Implement method calls" ]

--
-- Full translation
--

lowIRReprCode :: LowIRRepr -> [String]
lowIRReprCode (LowIRRepr fields strings methods) =
    [ "# TODO: Write full translation code" ]
