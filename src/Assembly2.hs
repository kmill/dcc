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
data RorM = Reg Reg
          | Mem MemAddr
data Flag = FlagZ | FlagNZ
          | FlagL | FlagLE | Flag GE | Flag G
          | FlagE | FlagNE

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
--  call r/m64  (indirect call)
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
--  imulq r/m64  (%rdx:%rax <- %rax * r/m64)
--  imulq r/m64, r64  (r64 <- r64 * r/m64)
--  imulq imm32, r/m64, r64  (r64 <- imm32 * r/m64)
--
--  idivq r/m64  (rem=%rdx,quot=%rax <- %rdx:%rax / r/m64)
--
--  shlq imm8, r/m64
--  shrq imm8, r/m64  (n.b. unsigned)
--  sarq imm8, r/m64  (n.b. signed)
--
--  cmpq imm32/r64, r/m64

-- look at cmpxchg?


data Asm e x where
  Label     :: SourcePos -> Label                                 -> Asm C O
  Mov
  AddReg    :: SourcePos -> Reg -> 
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

