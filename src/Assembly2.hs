{-# LANGUAGE RankNTypes, GADTs, TypeFamilies #-}

module Assembly2 where

import IR2
import qualified Data.Map as Map
import Data.Graphs
import Data.List
import AST(SourcePos)
import Data.Int

data Reg = MReg X86Reg -- ^ a real machine register
         | SReg Int -- ^ a symbolic register
data Imm8 = Imm8 Int8
data Imm16 = Imm16 Int16
data Imm32 = Imm32 Int32 -- ^ a 32-bit sign-extended literal
           | Imm32BlockLabel Label Int32 -- ^ a label to a block with a displacement
           | Imm32Label String Int32 -- ^ a label with a displacement
data Imm64 = Imm64 Int64
           | Imm64BlockLabel Label Int64
           | Imm64Label String Int64
data Scalar = SOne | STwo | SFour | SEight
data MemAddr = MemAddr
    { baseReg :: Maybe RegName
    , displace :: Imm32
    , indexReg :: Maybe RegName
    , scalar :: Scalar }
data Flag = FlagZ | FlagNZ
          | FlagL | FlagLE | Flag GE | Flag G
          | FlagE | FlagNE

data OperIRM = IRM_I Imm32
            | IRM_R Reg
            | IRM_M MemAddr
data OperIR = IR_I Imm32
           | IR_R Reg
data OperRM = RM_R Reg
           | RM_M MemAddr

instance Show OperIRM where
    show (IRM_I imm) = show imm
    show (IRM_R reg) = show reg
    show (IRM_M addr) = show addr
instance Show OperIR where
    show (IR_I imm) = show imm
    show (IR_R reg) = show reg
instance Show OperRM where
    show (RM_R reg) = show reg
    show (RM_M mem) = show mem

-- | Can the 64-bit immediate be represented as a 32-bit immediate?
-- We assume all labels fit comfortably in 32-bit registers.
checkIf32able :: Imm64 -> Bool
checkIf32able imm
    = x >= fromIntegral (minBound :: Int32)
      && x <= fromIntegral (maxBound :: Int32)
    where x = case imm of
                Imm64 v -> v
                Imm64BlockLabel _ v -> v
                Imm64Label _ v -> v
-- | Performs the conversion of 64-bit immediates to 32-bit
-- immediates.
to32Imm :: Imm64 -> Imm32
to32Imm (Imm64 x) = Imm32 $ fromIntegral x
to32Imm (Imm64Block l x) = Imm32Block l $ fromIntegral x
to32Imm (Imm64Label s x) = Imm32Label s $ fromIntegral x

checkIfScalar :: Int64 -> Bool
checkIfScalar x = x `elem` [1,2,4,8]

intToScalar :: Int64 -> Scalar
intToScalar 1 = SOne
intToScalar 2 = STwo
intToScalar 4 = SFour
intToScalar 8 = SEight
intToScalar _ = error "Not a scalar"

instance Show Reg where
    show (MReg reg) = show reg
    show (SReg i) = "%s" ++ show i

instance Show Imm8 where
    show (Imm8 x) = show x
instance Show Imm16 where
    show (Imm16 x) = show x
instance Show Imm32 where
    show (Imm32 x) = show x
    show (Imm32BlockLabel l d)
        = "(" ++ show l ++ " + " ++ show d ++ ")"
    show (Imm32Label s d)
        = "(" ++ show s ++ " + " ++ show d ++ ")"
instance Show Imm64 where
    show (Imm64 x) = show x
    show (Imm64BlockLabel l d)
        = "(" ++ show l ++ " + " ++ show d ++ ")"
    show (Imm64Label s d)
        = "(" ++ show s ++ " + " ++ show d ++ ")"
instance Show Scalar where
    show SOne = error "shouldn't try to display scalar of one"
    show STwo = "2"
    show SFour = "4"
    show SEight = "8"

instance Show MemAddr where
    show (MemAddr Nothing lit Nothing _)
        = show lit
    show (MemAddr (Just base) lit Nothing _)
        = show lit ++ "(" ++ show base ++ ")"
    show (MemAddr Nothing lit (Just index) SOne)
        = show lit ++ "(, " ++ show index ++ ")"
    show (MemAddr Nothing lit (Just index) s)
        = show lit ++ "(, " ++ show index ++ ", " ++ show s")"
    show (MemAddr (Just base) lit (Just index) SOne)
        = show lit ++ "(" ++ show base ++ ", "
          ++ show index ++ ")"
    show (MemAddr (Just base) lit (Just index) s)
        = show lit ++ "(" ++ show base ++ ", "
          ++ show index ++ ", " ++ show s ")"

instance Show Flag where
    show FlagZ = "z"
    show FlagNZ = "nz"
    show FlagL = "l"
    show FlagLE = "le"
    show FlagG = "g"
    show FlagGE = "ge"
    show FlagE = "e"
    show FlagNE = "ne"

---
--- Valid x86
---
-- Legend:
--  r64 is a 64-bit register
--  m64 is a 64-bit memory location
--  imm32 is a 32-bit immediate
--  imm64 is a 64-bit immediate
--  rel32 is 32-bit immediate relative to RIP

-- srcOpers = irm, ir, i_64, rm
-- dstOpers = r, m

-- moves
--  movq imm32/r64/m64, r64
--  movq imm32/r64, m64
--  movq imm64, r64
-- maybe :
--  movq (imm64), %rax  (indirect from 64-bit)
--  movq %rax, (imm64)

-- conditional moves. cc is a Flag
--  cmovccq r64/m64, r64

-- procedure linkage
--  enter $x, $0
--  leave
--  call rel32  (normal call)
--  call r64/m64  (indirect call)
--  ret
--  ret imm16 (pop this many bytes from stack)


-- load effective address.  mem is like m64, but the address is put
-- into the r64
--  lea mem, r64

-- stack operations
--  pushq imm32/r64/m64
--  popq r64/m64


-- branches. cc is a Flag
--  jmp imm32/r64/m64
--  jcc rel32

-- ALU operations. xxx is add/sub/xor
--  xxxq imm32/r64/m64, r64
--  xxxq imm32/r64, m64
--
--  incq r64/m64
--  decq r64/m64
--
--  imulq r64/m64  (%rdx:%rax <- %rax * r/m64)
--  imulq r64/m64, r64  (r64 <- r64 * r/m64)
--  imulq imm32, r64/m64, r64  (r64 <- imm32 * r/m64)
--
--  idivq r64/m64  (rem=%rdx,quot=%rax <- %rdx:%rax / r/m64)
--
--  shlq imm8, r64/m64
--  shrq imm8, r64/m64  (n.b. unsigned)
--  sarq imm8, r64/m64  (n.b. signed)
--
--  cmpq imm32/r64, r64/m64
--
--  negq r64/m64

-- look at cmpxchg?

data ALUOp = Add | Sub | Xor
instance Show ALUOp where
    show Add = "add"
    show Sub = "sub"
    show Xor = "xor"

data Asm e x where
  Label     :: SourcePos -> Label                                 -> Asm C O

  Spill :: SourcePos -> Reg -> String -> Asm O O
  Reload :: SourcePos -> String -> Reg -> Asm O O

  MovIRMtoR :: SourcePos -> OperIRM -> Reg -> Asm O O
  MovIRtoM  :: SourcePos -> OperIR -> MemAddr -> Asm O O
  Mov64toR  :: SourcePos -> Imm64 -> Reg -> Asm O O

  CMovRMtoR :: SourcePos -> Flag -> OperRM -> Reg -> Asm O O

  Enter :: SourcePos -> Int -> Asm C O
  Leave :: SourcePos -> Asm O O

  Call :: SourcePos -> OperIRM -> Asm O O
  Ret :: SourcePos -> Asm O C
  RetPop :: SourcePos -> Imm16 -> Asm O C

  Lea :: SourcePos -> MemAddr -> Reg -> Asm O O

  Push :: SourcePos -> OperIRM -> Asm O O
  Pop :: SourcePos -> OperRM -> Asm O O

  Jmp :: SourcePos -> Imm32 -> Asm O C
  JCond :: SourcePos -> Flag -> Imm32 -> Asm O C

  ALU_IRMtoR :: SourcePos -> ALUOp -> OperIRM -> Reg -> Asm O O
  ALU_IRtoM :: SourcePos -> ALUOp -> OperIR -> MemAddr -> Asm O O
  Cmp :: SourcePos -> OperIR -> OperRM -> Asm O O

  Inc :: SourcePos -> OperRM -> Asm O O
  Dec :: SourcePos -> OperRM -> Asm O O

  Neg :: SourcePos -> OperRM -> Asm O O

  IMulRAX :: SourcePos -> OperRM -> Asm O O
  IMulRM :: SourcePos -> OperRM -> Reg -> Asm O O
  IMulImm :: SourcePos -> Imm32 -> OperRM -> Reg -> Asm O O

  IDiv :: SourcePos -> OperRM -> Asm O O

  -- shift left/right
  Shl :: SourcePos -> Imm8 -> OperRM -> Asm O O
  Shr :: SourcePos -> Imm8 -> OperRM -> Asm O O
  -- shift arithmetic right (beware, different from idiv!)
  Sar :: SourcePos -> Imm8 -> OperRM -> Asm O O

  Nop :: SourcePos -> Asm O O
  
instance NonLocal Asm where
  entryLabel (Label _ lbl) = lbl
  successors (Jmp _ 
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

