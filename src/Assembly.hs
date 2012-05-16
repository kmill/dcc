{-# LANGUAGE RankNTypes, GADTs, TypeFamilies, MultiParamTypeClasses #-}

module Assembly where

import Compiler.Hoopl
import qualified IR as I
import qualified Data.Map as Map
import Data.List
import AST(SourcePos, showPos)
import Data.Int
import Text.Printf
import Control.Monad
import Data.Maybe
import Debug.Trace

-- | The assembly form is our low IR.
data LowIRRepr = LowIRRepr
    { lowIRFields :: [LowIRField]
    , lowIRStrings :: [(String, SourcePos, String)]
    , lowIRIPCSize :: Int
    , lowIRMethods :: [I.Method]
    , lowIRGraph :: Graph Asm C C }
data LowIRField = LowIRField SourcePos String Int64


data Reg = MReg X86Reg -- ^ a real machine register
         | SReg String -- ^ a symbolic register
           deriving (Eq, Ord)

x86Reg :: Reg -> X86Reg
x86Reg (MReg r) = r
x86Reg _ = error "getReg on non-MReg :-("

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

irToIRM :: OperIR -> OperIRM
irToIRM (IR_I i) = IRM_I i
irToIRM (IR_R r) = IRM_R r

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

data SpillLoc = SpillID Int
              | SpillSID String
              | SpillArg Int
              | SpillIPC Int
                deriving (Eq, Ord, Show)

fixedSpill :: SpillLoc -> Bool
fixedSpill (SpillArg _) = True
fixedSpill (SpillID _) = False
fixedSpill (SpillSID _) = False
fixedSpill (SpillIPC _) = True

type SpillLocSupply = [SpillLoc]

freeSpillLocs :: SpillLocSupply
freeSpillLocs = map SpillID [0..]

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

intToScalar :: Int64 -> Maybe Scalar
intToScalar 1 = Just SOne
intToScalar 2 = Just STwo
intToScalar 4 = Just SFour
intToScalar 8 = Just SEight
intToScalar _ = Nothing

instance Show Reg where
    show (MReg reg) = show reg
    show (SReg i) = "%" ++ i

instance Show Imm8 where
    show (Imm8 x) = "$" ++ show x
instance Show Imm16 where
    show (Imm16 x) = "$" ++ show x
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

showDisp :: Imm32 -> String
showDisp (Imm32 0) = ""
showDisp d = show d

instance Show MemAddr where
    show (MemAddr Nothing lit Nothing _)
        -- Rip-relative addressing!
        -- http://www.x86-64.org/documentation/assembly.html
        = showDisp lit ++ "(%rip)"
    show (MemAddr (Just base) lit Nothing _)
        = showDisp lit ++ "(" ++ show base ++ ")"
    show (MemAddr Nothing lit (Just index) SOne)
        = showDisp lit ++ "(, " ++ show index ++ ")"
    show (MemAddr Nothing lit (Just index) s)
        = showDisp lit ++ "(, " ++ show index ++ ", " ++ show s ++ ")"
    show (MemAddr (Just base) lit (Just index) SOne)
        = showDisp lit ++ "(" ++ show base ++ ", "
          ++ show index ++ ")"
    show (MemAddr (Just base) lit (Just index) s)
        = showDisp lit ++ "(" ++ show base ++ ", "
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

  Spill :: SourcePos -> Reg -> SpillLoc -> Asm O O
  Reload :: SourcePos -> SpillLoc -> Reg -> Asm O O

  MovIRMtoR :: SourcePos -> OperIRM -> Reg -> Asm O O
  MovIRtoM  :: SourcePos -> OperIR -> MemAddr -> Asm O O
  Mov64toR  :: SourcePos -> Imm64 -> Reg -> Asm O O

  CMovRMtoR :: SourcePos -> Flag -> OperRM -> Reg -> Asm O O

  -- Takes 1) the number of arguments and 2) the amount of stack
  -- space.  Not actually "enter" instruction!
  Enter :: SourcePos -> Label -> Int -> Int32 -> Asm C O
  -- Takes whether it returns something in RAX and how much stack
  -- space should be freed.  Not actually "leave" instruction!
  Leave :: SourcePos -> Bool -> Int32 -> Asm O C

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
  
  -- | Takes a label to a function along with what to actually jump
  -- to.
  InternalFunc :: SourcePos -> Label -> Imm32 -> Asm O C
  
  -- | For Mac OS X compatibility mode
--  Realign :: SourcePos -> Int -> Asm O O
--  Unrealign :: SourcePos -> Asm O O

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
  entryLabel (Enter _ lbl _ _) = lbl
  successors (Jmp _ (Imm32BlockLabel l 0)) = [l]
  successors (Jmp _ _) = []
  successors (JCond _ _ (Imm32BlockLabel tr 0) fa) = [tr, fa]
  successors (JCond _ _ _ fa) = [fa]
  successors (Leave _ _ _) = []
  successors (Ret _ _) = []
  successors (RetPop _ _ _) = []
  successors (ExitFail _) = []
  successors (InternalFunc _ fl (Imm32BlockLabel al 0)) = [al, fl]
  successors (InternalFunc _ fl _) = [fl]

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
  show (MovIRMtoR pos (IRM_I (Imm32 0)) b)
    | isJust (show32 b)  = let Just b' = show32 b
                           in printf "xorl %s, %s    # %s" b' b' (showPos pos)
    | otherwise = showBinOp "xorq" pos b b
  show (MovIRMtoR pos irm@(IRM_I (Imm32 i)) b)
    | i >= 0 && isJust (show32 b)
          = let Just b' = show32 b
            in printf "movl %s, %s    # %s" (show irm) b' (showPos pos)
  show (MovIRMtoR pos a b) = showBinOp "movq" pos a b
  show (MovIRtoM pos a b) = showBinOp "movq" pos a b
  show (Mov64toR pos a b) = printf "%s $%s, %s      # %s"
                            "movq" (show a) (show b) (showPos pos)

  show (CMovRMtoR pos flag a b) = showBinOp opcode pos a b
            where opcode = "cmov" ++ show flag ++ "q"

  show (Enter pos lbl nargs st)
      = printf "%s: %s  # %d args  %s"
        (show lbl) adjSP nargs (showPos pos)
      where adjSP = case st of
                      0 -> ""
                      _ -> printf "subq $%d, %%rsp" st
  show (Leave pos returns st) = fixsp ++ showNullOp "ret" pos
                                ++ (if not returns then " (void method)" else "")
      where fixsp = if st == 0 then "" else printf "addq $%d, %%rsp\n   " st

  show (Call pos nargs func) = showUnOp "call" pos func
  show (Callout pos nargs func) = showUnOp "call" pos func
  show (InternalFunc pos flab alab)
      = showUnOp "jmp" pos alab ++ " (InternalFunc)"
  show (Ret pos returns)
      = showNullOp "ret" pos
        ++ (if not returns then " (void method)" else "")
  show (RetPop pos returns num)
      = showUnOp "ret" pos num
        ++ (if not returns then " (void method)" else "")
  show (ExitFail pos)
      = "# exited by failure. " ++ showPos pos
--   show (Realign pos i)
--        = "# realign goes here for --mac"
--   show (Unrealign pos)
--       = "# unrealign goes here for --mac"

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

instance Mnemonic Int64 Reg where
    mov p i d = if checkIf32Bit i
                then MovIRMtoR p (IRM_I $ Imm32 $ fromIntegral i) d
                else Mov64toR p (Imm64 i) d

---
--- Registers
---

-- | This is the order of arguments in registers for the ABI.
-- 'Nothing' represents that the argument comes from the stack.
argOrder :: [Maybe X86Reg]
argOrder = (map Just [RDI, RSI, RDX, RCX, R8, R9]) ++ nothings
    where nothings = Nothing:nothings

argStoreLocations :: Int32 -> [Either MemAddr Reg]
argStoreLocations dsp = map (Right . MReg) [RDI, RSI, RDX, RCX, R8, R9]
                        ++ map (Left . makeMem) [dsp, dsp+8..]
    where makeMem d = MemAddr (Just $ MReg RSP) (Imm32 d) Nothing SOne

argStackDepth :: [Int]
argStackDepth = [no, no, no, no, no, no] ++ [16, 16+8..]
    where no = error "argStackDepth for non-stack-arg :-("

argLocation :: [Either SpillLoc Reg]
argLocation = map (Right . MReg) [RDI, RSI, RDX, RCX, R8, R9]
              ++ map (Left . SpillArg) [0,1..]

---- | Gives a midir expression for getting any particular argument.
--argExprs :: SourcePos -> [Expr VarName]
--argExprs pos = (map (Var pos . MReg) [RDI, RSI, RDX, RCX, R8, R9])
--               ++ (map (\d -> Load pos (BinOp pos OpAdd (Lit pos d) (Var pos (MReg RBP))))
--                   [16, 16+8..])

callerSaved :: [X86Reg]
callerSaved = [R10, R11] ++ [RDI, RSI, RDX, RCX, R8, R9]

calleeSaved :: [X86Reg]
calleeSaved = [RBX, R12, R13, R14, R15, RBP]

-- | All the registers but RSP, which cannot be used (otherwise bad
-- things will happen!)  It might be possible to use RSP, but too much
-- care would need to be taken to make it worthwhile.
usableRegisters :: [X86Reg]
usableRegisters = [RAX, RBX, RCX, RDX, RBP, RSI, RDI
                   ,R8, R9, R10, R11, R12, R13, R14, R15]

usableRegisters' :: [Reg]
usableRegisters' = map MReg usableRegisters

numUsableRegisters :: Int
numUsableRegisters = length usableRegisters

data X86Reg = RAX -- temp reg, return value
            | RBX -- callee-saved
            | RCX -- 4th arg
            | RDX -- 3rd arg
            | RSP -- stack pointer
            | RBP -- "base pointer" (callee-saved)
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

show32 :: Reg -> Maybe String
show32 (MReg RAX) = Just "%eax"
show32 (MReg RBX) = Just "%ebx"
show32 (MReg RCX) = Just "%ecx"
show32 (MReg RDX) = Just "%edx"
show32 (MReg RSP) = Just "%esp"
show32 (MReg RBP) = Just "%ebp"
show32 (MReg RSI) = Just "%esi"
show32 (MReg RDI) = Just "%edi"
show32 _ = Nothing

class AsmRename x where
    -- | Takes a function on registers and something, and replaces the
    -- registers in the something.
    mapArg :: (Reg -> Maybe Reg) -> x -> Maybe x

instance AsmRename Reg where
    mapArg f r = f r
instance AsmRename MemAddr where
    mapArg f m = let br = baseReg m
                     ir = indexReg m
                     (brm, irm) = (f `fmap` br, f `fmap` ir)
                     changed (Just (Just _)) = True
                     changed _ = False
                     new _ (Just (Just v)) = Just v
                     new v _ = v
                     (br', ir') = (new br brm, new ir irm)
                 in if changed brm || changed irm
                    then return $ MemAddr
                             { baseReg = br'
                             , displace = displace m
                             , indexReg = ir'
                             , scalar = scalar m }
                    else Nothing 

instance AsmRename OperIRM where
    mapArg f (IRM_I i) = Nothing
    mapArg f (IRM_R r) = IRM_R `fmap` f r
    mapArg f (IRM_M m) = IRM_M `fmap` mapArg f m
instance AsmRename OperIR where
    mapArg f (IR_I i) = Nothing
    mapArg f (IR_R r) = IR_R `fmap` f r
instance AsmRename OperRM where
    mapArg f (RM_R r) = RM_R `fmap` f r
    mapArg f (RM_M m) = RM_M `fmap` mapArg f m

mmaybe :: [(a, Maybe a)] -> Maybe [a]
mmaybe mvals = do msum $ map snd mvals
                  return $ map (uncurry fromMaybe) mvals

mmaybe2 :: ((a, Maybe a), (b, Maybe b)) -> Maybe (a, b)
mmaybe2 ((_, Nothing), (_, Nothing)) = Nothing
mmaybe2 ((a, ma), (b, mb)) = Just (fromMaybe a ma, fromMaybe b mb)

mmaybe3 :: ((a, Maybe a), (b, Maybe b), (c, Maybe c)) -> Maybe (a, b, c)
mmaybe3 ((_, Nothing), (_, Nothing), (_, Nothing)) = Nothing
mmaybe3 ((a, ma), (b, mb), (c, mc)) = Just (fromMaybe a ma, fromMaybe b mb, fromMaybe c mc)

mapAsm :: forall e x . (Reg -> Maybe Reg) -> (Reg -> Maybe Reg) -> Asm e x -> Maybe (Asm e x)
mapAsm fs fd n
    = case n of
        Label{} -> Nothing
        
        Spill pos r spillloc -> do r' <- fs' r
                                   return $ Spill pos r' spillloc
        Reload pos spillloc r -> do r' <- fd' r
                                    return $ Reload pos spillloc r'
        
        MovIRMtoR pos s d -> do (s', d') <- mmaybe2 ((s, fs' s), (d, fd' d))
                                return $ MovIRMtoR pos s' d'
        MovIRtoM pos s m -> do (s', m') <- mmaybe2 ((s, fs' s), (m, fs' m))
                               return $ MovIRtoM pos s' m'
        Mov64toR pos i d -> do d' <- fd' d
                               return $ Mov64toR pos i d'

        CMovRMtoR pos fl s d -> do (s', dSource', dDest') <- mmaybe3 ((s, fs' s)
                                                                     ,(d, fs' d)
                                                                     ,(d, fd' d))
                                   when (dSource' /= dDest') $
                                        error $ printf "source and dest not equal in %s!" (show n)
                                   return $ CMovRMtoR pos fl s' dDest'
        
        Enter{} -> Nothing
        Leave{} -> Nothing
        
        Call{} -> Nothing
        Callout{} -> Nothing
        InternalFunc{} -> Nothing
        Ret{} -> Nothing
        RetPop{} -> Nothing
        ExitFail{} -> Nothing
        
        Lea pos s d -> do (s', d') <- mmaybe2 ((s, fs' s), (d, fd' d))
                          return $ Lea pos s' d'
        
        Push pos s -> do s' <- fs' s
                         return $ Push pos s'
        Pop pos (RM_R rd) -> do d' <- fd' rd
                                return $ Pop pos (RM_R d')
        Pop pos (RM_M ms) -> do ms' <- fs' ms
                                return $ Pop pos (RM_M ms')
        
        Jmp{} -> Nothing
        JCond{} -> Nothing
        
        ALU_IRMtoR pos op s d -> do (s', dSource', dDest') <- mmaybe3 ((s, fs' s)
                                                                      ,(d, fs' d)
                                                                      ,(d, fd' d))
                                    when (dSource' /= dDest') $
                                         error $ printf "source and dest not equal in %s!" (show n)
                                    return $ ALU_IRMtoR pos op s' dDest'
        ALU_IRtoM pos op s m -> do (s', m') <- mmaybe2 ((s, fs' s), (m, fs' m))
                                   return $ ALU_IRtoM pos op s' m'
        Cmp pos s1 s2 -> do (s1', s2') <- mmaybe2 ((s1, fs' s1), (s2, fs' s2))
                            return $ Cmp pos s1' s2'
        Test pos s1 s2 -> do (s1', s2') <- mmaybe2 ((s1, fs' s1), (s2, fs' s2))
                             return $ Test pos s1' s2'
        
        Inc pos sd -> doUnaryRM (Inc pos) sd
        Dec pos sd -> doUnaryRM (Dec pos) sd
        Neg pos sd -> doUnaryRM (Neg pos) sd
        
        IMulRAX pos s -> do s' <- fs' s
                            return $ IMulRAX pos s'
        IMulRM pos s d -> do (s', dSource', dDest') <- mmaybe3 ((s, fs' s)
                                                               ,(d, fs' d)
                                                               ,(d, fd' d))
                             when (dSource' /= dDest') $
                                  error $ printf "source and dest not equal in %s!" (show n)
                             return $ IMulRM pos s' dDest'
        IMulImm pos i s d -> do (s', d') <- mmaybe2 ((s, fs' s), (d, fd' d))
                                return $ IMulImm pos i s' d'
        
        IDiv pos s -> do s' <- fs' s
                         return $ IDiv pos s'
        Cqo{} -> Nothing
        
        Shl pos i rm -> doUnaryRM (Shl pos i) rm
        Shr pos i rm -> doUnaryRM (Shr pos i) rm
        Sar pos i rm -> doUnaryRM (Sar pos i) rm
        
        Nop{} -> Nothing
        
    where fs', fd' :: AsmRename x => x -> Maybe x
          fs' = mapArg fs
          fd' = mapArg fd
          
          doUnaryRM :: (OperRM -> Asm O O) -> OperRM -> Maybe (Asm O O)
          doUnaryRM cons (RM_R rd)
              = do (rdSource', rdDest') <- mmaybe2 ((rd, fs' rd)
                                                   ,(rd, fd' rd))
                   when (rdSource' /= rdDest') $
                        error $ printf "source and dest not equal in %s!" (show n)
                   return $ cons (RM_R rdDest')
          doUnaryRM cons (RM_M m) = do m' <- fs' m
                                       return $ cons (RM_M m')
