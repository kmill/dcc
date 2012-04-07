module Assembly2 where

import IR2
import qualified Data.Map as Map
import Data.Graphs
import Text.ParserCombinators.Parsec.Pos

data RegName = FReg X86Reg
             | SymReg Int64

instance Show RegName where
  show (FReg reg) = show reg
  show (SymReg val) = "#Where goes Reg " ++ (show val)

data ConstLoc = Label
              | Int64

data MemLoc = MemConst Int64
            | LabelLoc Label
            | RegLoc RegName
            | RegAddr { baseReg :: RegName
                      , displace :: Int64
                      , offsetReg :: Maybe RegName
                      , scalar :: Int64 }

instance Show MemLoc where
  show (MemConst val) = ""
  show (LabelLoc lab) = lab
  show (RegLoc reg) = show reg
  show (RegAddr reg 0 Nothing _) = show reg
  show (RegAddr reg disp Nothing _) = disp ++ "(" ++ (show reg) ++ ")"
  show (RegAddr reg 0 (Just oReg) scal) = "(" ++ (show reg) ++ ", " ++ (show oReg) ++ ", " ++ scal ++  ")"
  show (RegAddr reg disp (Just oReg) scal) = disp ++ "(" ++ (show reg) ++ ", " ++ (show oReg) ++ ", " ++ scal ++  ")"
  
data Asm e x where
  LabelAsm  :: SourcePos -> Label                                 -> Asm C O
  AddAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O
  SubAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O
  MulAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O
  DivAsm    :: SourcePos -> MemLoc                                -> Asm O O
  ModAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O
  CmpAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O
  MovAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O
  NegAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O
  XorAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O
  ShlAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O
  ShrAsm    :: SourcePos -> MemLoc -> RegLoc RegName              -> Asm O O  
  CMovAsm   :: SourcePos -> CmpSInstr -> MemLoc -> RegLoc RegName -> Asm O O
  StoreAsm  :: SourcePos -> MemLoc -> MemLoc                      -> Asm O O
  LoadAsm   :: SourcePos -> MemLoc -> MemLoc                      -> Asm O O
  JmpAsm    :: SourcePos -> Label                                 -> Asm O O
  NopAsm    :: SourcePos                                          -> Asm O O
  CJmpAsm   :: SourcePos -> CmpSInstr -> Label -> Label           -> Asm O C
  RetAsm    :: SourcePos                                          -> Asm O C
  
data CmpSIntr = CmpLT | CmpGT | CmpLTE | CmpGTE | CmpEQ | CmpNEQ

instance NonLocal Asm where
  entryLavel (Label _ lbl) = lbl
  successors (CJmpAsm _ tr fa) = [tr, fa]
  successors (RetAsm _) = []

instance Show Asm where
  show (LabelAsm _ l) = l ++ ":"
  show (AddAsm _ op1 op2) = binOp "addq" op1 op2
  show (SubAsm _ op1 op2) = binOp "subq" op1 op2
  show (MulAsm _ op1 op2) = binOp "imulq" op1 op2
  show (DivAsm _ op1)     = uniOp "idivq" op1 
  show (ModAsm _ op1 op2) = binOp "modq" op1 op2
  show (CmpAsm _ op1 op2) = binOp "addq" op1 op2
  show (MovAsm _ op1 op2) = binOp "addq" op1 op2
  show (NegAsm _ op1 op2) = binOp "addq" op1 op2
  show (XorAsm _ op1 op2) = binOp "addq" op1 op2
  show (ShlAsm _ op1 op2) = binOp "addq" op1 op2
  show (ShrAsm _ op1 op2) = binOp "addq" op1 op2
  show (CMovAsm _ csi op1 op2) = binOp ("cmov" ++ (show csi)) op1 op2
  show (StoreAsm _ op1 op2) = binOp "movq" op1 op2
  show (LoadAsm _ op1 op2) = binOp "movq" op1 op2
  show (JmpAsm _ op1) = uniOp "jmp" op1
  show (CJmpAsm _ csi op1 op2) = binOp ("j" ++ (show csi)) op1 op2
  show (RetAsm _) = "return"
  show (NopAsm _) = "nop"

binOp :: String -> MemLoc -> MemLoc -> String
binOp op o1 o2 = op ++ " " ++ (show o1) ++ " " ++ (show o2)

uniOp :: String -> MemLoc -> String
uniOp op o1 = op ++ " " ++ (show o1)

instance Show CmpSIntr where
  show CmpLT = "l"
  show CmpGT = "g"
  show CmpLTE = "le"
  show CmpGTE = "ge"
  show CmpEQ = "e"
  show CmpNEQ = "ne"