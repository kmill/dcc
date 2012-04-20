{-# LANGUAGE RankNTypes, GADTs, TypeFamilies, MultiParamTypeClasses #-}

module Assembly where

import Compiler.Hoopl
import qualified IR as I
import qualified Data.Map as Map
import Data.List
import AST(SourcePos, showPos)
import Data.Int
import Text.Printf

-- | The assembly form is our low IR.
data LowIRRepr = LowIRRepr
    { lowIRFields :: [LowIRField]
    , lowIRStrings :: [(String, SourcePos, String)]
    , lowIRMethods :: [I.Method]
    , lowIRGraph :: Graph Asm C C }
data LowIRField = LowIRField SourcePos String Int64


data Reg = MReg X86Reg -- ^ a real machine register
         | SReg String -- ^ a symbolic register
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
    { baseReg :: Maybe Reg
    , displace :: Imm32
    , indexReg :: Maybe Reg
    , scalar :: Scalar }
data Flag = FlagZ | FlagNZ
          | FlagL | FlagLE | FlagGE | FlagG
          | FlagE | FlagNE

data OperIRM = IRM_I Imm32
            | IRM_R Reg
            | IRM_M MemAddr
data OperIR = IR_I Imm32
           | IR_R Reg
data OperRM = RM_R Reg
           | RM_M MemAddr

rmToIRM :: OperRM -> OperIRM
rmToIRM (RM_R r) = IRM_R r
rmToIRM (RM_M m) = IRM_M m

instance Show OperIRM where
    show (IRM_I imm) = "$" ++ show imm
    show (IRM_R reg) = show reg
    show (IRM_M addr) = show addr
instance Show OperIR where
    show (IR_I imm) = "$" ++ show imm
    show (IR_R reg) = show reg
instance Show OperRM where
    show (RM_R reg) = show reg
    show (RM_M mem) = show mem

checkIf32Bit :: Int64 -> Bool
checkIf32Bit x
    = x >= fromIntegral (minBound :: Int32)
      && x <= fromIntegral (maxBound :: Int32)

-- | Can the 64-bit immediate be represented as a 32-bit immediate?
-- We assume all labels fit comfortably in 32-bit registers.
checkIf32able :: Imm64 -> Bool
checkIf32able imm
    = checkIf32Bit x
    where x = case imm of
                Imm64 v -> v
                Imm64BlockLabel _ v -> v
                Imm64Label _ v -> v
-- | Performs the conversion of 64-bit immediates to 32-bit
-- immediates.
to32Imm :: Imm64 -> Imm32
to32Imm (Imm64 x) = Imm32 $ fromIntegral x
to32Imm (Imm64BlockLabel l x) = Imm32BlockLabel l $ fromIntegral x
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
    show (SReg i) = "%" ++ i

instance Show Imm8 where
    show (Imm8 x) = "$" ++ show x
instance Show Imm16 where
    show (Imm16 x) = show x
instance Show Imm32 where
    show (Imm32 x) = show x
    show (Imm32BlockLabel l 0) = show l
    show (Imm32BlockLabel l d)
        = "(" ++ show l ++ " + " ++ show d ++ ")"
    show (Imm32Label s 0) = s
    show (Imm32Label s d)
        = "(" ++ s ++ " + " ++ show d ++ ")"
instance Show Imm64 where
    show (Imm64 x) = show x
    show (Imm64BlockLabel l 0) = show l
    show (Imm64BlockLabel l d)
        = "(" ++ show l ++ " + " ++ show d ++ ")"
    show (Imm64Label s 0) = s
    show (Imm64Label s d)
        = "(" ++ s ++ " + " ++ show d ++ ")"
instance Show Scalar where
    show SOne = error "shouldn't try to display scalar of one"
    show STwo = "2"
    show SFour = "4"
    show SEight = "8"

instance Show MemAddr where
    show (MemAddr Nothing lit Nothing _)
        -- Rip-relative addressing is cheaper!
        -- http://www.x86-64.org/documentation/assembly.html
        = show lit ++ "(%rip)"
    show (MemAddr (Just base) lit Nothing _)
        = show lit ++ "(" ++ show base ++ ")"
    show (MemAddr Nothing lit (Just index) SOne)
        = show lit ++ "(, " ++ show index ++ ")"
    show (MemAddr Nothing lit (Just index) s)
        = show lit ++ "(, " ++ show index ++ ", " ++ show s ++ ")"
    show (MemAddr (Just base) lit (Just index) SOne)
        = show lit ++ "(" ++ show base ++ ", "
          ++ show index ++ ")"
    show (MemAddr (Just base) lit (Just index) s)
        = show lit ++ "(" ++ show base ++ ", "
          ++ show index ++ ", " ++ show s ++ ")"

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

data ALUOp = Add | Sub | And | Xor
instance Show ALUOp where
    show Add = "add"
    show Sub = "sub"
    show And = "and"
    show Xor = "xor"

data Asm e x where
  Label     :: SourcePos -> Label -> Asm C O

  Spill :: SourcePos -> Reg -> String -> Asm O O
  Reload :: SourcePos -> String -> Reg -> Asm O O

  MovIRMtoR :: SourcePos -> OperIRM -> Reg -> Asm O O
  MovIRtoM  :: SourcePos -> OperIR -> MemAddr -> Asm O O
  Mov64toR  :: SourcePos -> Imm64 -> Reg -> Asm O O

  CMovRMtoR :: SourcePos -> Flag -> OperRM -> Reg -> Asm O O

  Enter :: SourcePos -> Label -> Int -> Asm C O
  Leave :: SourcePos -> Asm O O

  -- | Int is the number of arguments (to know which registers are
  -- used)
  Call :: SourcePos -> Int -> Imm32 -> Asm O O
  Callout :: SourcePos -> Int -> Imm32 -> Asm O O
  -- | The boolean is whether it cares about the return value (so we
  -- know whether to save RAX for the return)
  Ret :: SourcePos -> Bool -> Asm O C
  RetPop :: SourcePos -> Bool -> Imm16 -> Asm O C
  -- | This doesn't actually do anything but close off a block. It is
  -- expected that the code has called "exit" before reaching this.
  ExitFail :: SourcePos -> Asm O C
  
  -- | For Mac OS X compatibility mode
  Realign :: SourcePos -> Int -> Asm O O
  Unrealign :: SourcePos -> Asm O O

  Lea :: SourcePos -> MemAddr -> Reg -> Asm O O

  Push :: SourcePos -> OperIRM -> Asm O O
  Pop :: SourcePos -> OperRM -> Asm O O

  Jmp :: SourcePos -> Imm32 -> Asm O C
  -- | label is if false (the "fall-through")
  JCond :: SourcePos -> Flag -> Imm32 -> Label -> Asm O C

  ALU_IRMtoR :: SourcePos -> ALUOp -> OperIRM -> Reg -> Asm O O
  ALU_IRtoM :: SourcePos -> ALUOp -> OperIR -> MemAddr -> Asm O O
  Cmp :: SourcePos -> OperIR -> OperRM -> Asm O O
  Test :: SourcePos -> OperIR -> OperRM -> Asm O O

  Inc :: SourcePos -> OperRM -> Asm O O
  Dec :: SourcePos -> OperRM -> Asm O O

  Neg :: SourcePos -> OperRM -> Asm O O

  IMulRAX :: SourcePos -> OperRM -> Asm O O
  IMulRM :: SourcePos -> OperRM -> Reg -> Asm O O
  IMulImm :: SourcePos -> Imm32 -> OperRM -> Reg -> Asm O O

  IDiv :: SourcePos -> OperRM -> Asm O O
  Cqo :: SourcePos -> Asm O O

  -- shift left/right
  Shl :: SourcePos -> Imm8 -> OperRM -> Asm O O
  Shr :: SourcePos -> Imm8 -> OperRM -> Asm O O
  -- shift arithmetic right (beware, different from idiv!)
  Sar :: SourcePos -> Imm8 -> OperRM -> Asm O O

  Nop :: SourcePos -> Asm O O
  
instance NonLocal Asm where
  entryLabel (Label _ lbl) = lbl
  entryLabel (Enter _ lbl _) = lbl
  successors (Jmp _ (Imm32BlockLabel l 0)) = [l]
  successors (Jmp _ _) = []
  successors (JCond _ _ (Imm32BlockLabel tr 0) fa) = [tr, fa]
  successors (JCond _ _ _ fa) = [fa]
  successors (Ret _ _) = []
  successors (RetPop _ _ _) = []
  successors (ExitFail _) = []

showNullOp :: String -> SourcePos -> String
showNullOp opcode pos = printf "%s        # %s"
                        opcode (showPos pos)
showUnOp :: Show a => String -> SourcePos -> a -> String
showUnOp opcode pos a = printf "%s %s        # %s"
                        opcode (show a) (showPos pos)
showBinOp :: (Show a, Show b) => String -> SourcePos -> a -> b -> String
showBinOp opcode pos a b = printf "%s %s, %s        # %s"
                           opcode (show a) (show b) (showPos pos)

instance Show (Asm e x) where
  show (Label pos l)
      = printf "%s:  # %s"
        (show l) (showPos pos)
  show (Spill pos reg sname)
      = printf "SPILL %s, %s  # %s"
        (show reg) (show sname) (showPos pos)
  show (Reload pos sname reg)
      = printf "RELOAD %s, %s  # %s"
        (show sname) (show reg) (showPos pos)
  show (MovIRMtoR pos a b) = showBinOp "movq" pos a b
  show (MovIRtoM pos a b) = showBinOp "movq" pos a b
  show (Mov64toR pos a b) = showBinOp "movq" pos a b

  show (CMovRMtoR pos flag a b) = showBinOp opcode pos a b
            where opcode = "cmov" ++ show flag ++ "q"

  show (Enter pos lbl st) = printf "%s: enter $%d, $0  # %s"
                            (show lbl) st (showPos pos)
  show (Leave pos) = showNullOp "leave" pos

  show (Call pos nargs func) = showUnOp "call" pos func
  show (Callout pos nargs func) = showUnOp "call" pos func
  show (Ret pos returns)
      = showNullOp "ret" pos
        ++ (if not returns then " (void method)" else "")
  show (RetPop pos returns num)
      = showUnOp "ret" pos num
        ++ (if not returns then " (void method)" else "")
  show (ExitFail pos)
      = "# exited by failure. " ++ showPos pos
  show (Realign pos i)
       = "# realign goes here for --mac"
  show (Unrealign pos)
      = "# unrealign goes here for --mac"

  show (Lea pos mem reg) = showBinOp "leaq" pos mem reg

  show (Push pos oper) = showUnOp "pushq" pos oper
  show (Pop pos oper) = showUnOp "popq" pos oper


  show (Jmp pos oper) = showUnOp "jmp" pos oper
  show (JCond pos flag oper fallthrough)
      = (showUnOp opcode pos oper) ++ " falls to " ++ show fallthrough
      where opcode = "j" ++ show flag

  show (ALU_IRMtoR pos op a b) = showBinOp ((show op) ++ "q") pos a b
  show (ALU_IRtoM pos op a b) = showBinOp ((show op) ++ "q") pos a b
  show (Cmp pos a b) = showBinOp "cmpq" pos a b
  show (Test pos a b) = showBinOp "testq" pos a b

  show (Inc pos oper) = showUnOp "incq" pos oper
  show (Dec pos oper) = showUnOp "decq" pos oper
  show (Neg pos oper) = showUnOp "negq" pos oper

  show (IMulRAX pos oper) = showUnOp "imulq" pos oper
  show (IMulRM pos a b) = showBinOp "imulq" pos a b
  show (IMulImm pos a b c) = printf "imulq $%s, %s, %s  # %s" -- :-O
                             (show a) (show b) (show c) (showPos pos)

  show (IDiv pos oper) = showUnOp "idivq" pos oper
  show (Cqo pos) = showNullOp "cqo" pos

  show (Shl pos a b) = showBinOp "shlq" pos a b
  show (Shr pos a b) = showBinOp "shrq" pos a b
  show (Sar pos a b) = showBinOp "sarq" pos a b

  show (Nop pos) = showNullOp "nop" pos

class Mnemonic src dst where
    mov :: SourcePos -> src -> dst -> Asm O O

instance Mnemonic Imm32 Reg where
    mov p s d = MovIRMtoR p (IRM_I s) d
instance Mnemonic Reg Reg where
    mov p s d = MovIRMtoR p (IRM_R s) d
instance Mnemonic MemAddr Reg where
    mov p s d = MovIRMtoR p (IRM_M s) d
instance Mnemonic Reg MemAddr where
    mov p s d = MovIRtoM p (IR_R s) d
instance Mnemonic Imm32 MemAddr where
    mov p s d = MovIRtoM p (IR_I s) d

---
--- Registers
---

-- | This is the order of arguments in registers for the ABI.
-- 'Nothing' represents that the argument comes from the stack.
argOrder :: [Maybe X86Reg]
argOrder = (map Just [RDI, RSI, RDX, RCX, R8, R9]) ++ nothings
    where nothings = Nothing:nothings

argStackDepth :: [Int]
argStackDepth = [no, no, no, no, no, no] ++ [16, 16+8..]
    where no = error "argStackDepth for non-stack-arg :-("

argLocation :: [Either MemAddr Reg]
argLocation = map (Right . MReg) [RDI, RSI, RDX, RCX, R8, R9]
              ++ map (Left . makeMem) [16,16+8..]
    where makeMem d = MemAddr (Just $ MReg RBP) (Imm32 d) Nothing SOne

---- | Gives a midir expression for getting any particular argument.
--argExprs :: SourcePos -> [Expr VarName]
--argExprs pos = (map (Var pos . MReg) [RDI, RSI, RDX, RCX, R8, R9])
--               ++ (map (\d -> Load pos (BinOp pos OpAdd (Lit pos d) (Var pos (MReg RBP))))
--                   [16, 16+8..])

callerSaved :: [X86Reg]
callerSaved = [R10, R11]

calleeSaved :: [X86Reg]
calleeSaved = [RBX, R12, R13, R14, R15]

data X86Reg = RAX -- temp reg, return value
            | RBX -- callee-saved
            | RCX -- 4th arg
            | RDX -- 3rd arg
            | RSP -- stack pointer
            | RBP -- base pointer (callee-saved)
            | RSI -- 2nd argument
            | RDI -- 1st argument
            | R8 -- 5th argument
            | R9 -- 6th argument
            | R10 -- temporary
            | R11 -- temporary
            | R12 -- callee-saved
            | R13 -- callee-saved
            | R14 -- callee-saved
            | R15 -- callee-saved
              deriving (Eq, Ord)

instance Show X86Reg where
    show RAX = "%rax"
    show RBX = "%rbx"
    show RCX = "%rcx"
    show RDX = "%rdx"
    show RSP = "%rsp"
    show RBP = "%rbp"
    show RSI = "%rsi"
    show RDI = "%rdi"
    show R8 = "%r8"
    show R9 = "%r9"
    show R10 = "%r10"
    show R11 = "%r11"
    show R12 = "%r12"
    show R13 = "%r13"
    show R14 = "%r14"
    show R15 = "%r15"
