{-# LANGUAGE FlexibleContexts, FlexibleInstances,
    MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances #-}

module IR where

import Text.ParserCombinators.Parsec
import Text.Printf
import Text.PrettyPrint.HughesPJ
import Data.Graphs
import AST
import Data.List
import Data.Int
import Data.Maybe
import Data.Either
import Control.Monad

boolToInt :: Bool -> Int64
boolToInt True = 1
boolToInt False = 0

data BasicBlock a b = BasicBlock
    { blockCode :: [a]
    , blockTest :: IRTest b
    , blockTestPos :: SourcePos }

type LowBasicBlock = BasicBlock LowIRInst LowOper
type MidBasicBlock = BasicBlock MidIRInst MidOper

-- | This is the order of arguments in registers for the ABI.
-- 'Nothing' represents that the argument comes from the stack.
argOrder :: [Maybe X86Reg]
argOrder = (map Just [RDI, RSI, RDX, RCX, R8, R9]) ++ nothings
    where nothings = Nothing:nothings

argStackDepth :: [Int]
argStackDepth = [no, no, no, no, no, no] ++ [16, 16+8..]
    where no = error "argStackDepth for non-stack-arg :-("

data IRTest b = IRTestTrue
              | IRTestFalse
              | IRTestBinOp CmpBinOp b b
              | IRTest b
              | IRTestNot b
              | IRReturn (Maybe b)
              | IRTestFail (Maybe String)

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
              
data RegName = X86Reg X86Reg
             | SymbolicReg Int

instance Show RegName where
    show (X86Reg r) = show r
    show (SymbolicReg i) = "%s" ++ show i

data BinOp = OpAdd
           | OpSub
           | OpMul
           | OpDiv
           | OpMod
           | OpBinCmp CmpBinOp
data UnOp = OpNeg
          | OpNot
          | OpDeref
--          | OpAddr
            
instance Show BinOp where
    show OpAdd = "+"
    show OpSub = "-"
    show OpMul = "*"
    show OpDiv = "/"
    show OpMod = "%"
    show (OpBinCmp cop) = show cop
instance Show UnOp where
    show OpNeg = "-"
    show OpNot = "!"
    show OpDeref = "*"
--    show OpAddr = "&"
            
data CmpBinOp = CmpLT
              | CmpGT
              | CmpLTE
              | CmpGTE
              | CmpEQ
              | CmpNEQ
--              | CmpAnd
--              | CmpOr

data CmpUnOp =  CmpZero
              | CmpNZero

---
--- LowIR
---

data LowIRRepr = LowIRRepr
    { lowIRFields :: [LowIRField]
    , lowIRStrings :: [(String, SourcePos, String)]
    , lowIRMethods :: [LowIRMethod] }
data LowIRField = LowIRField SourcePos String Int64
data LowIRMethod = LowIRMethod
    { lowIRMethodPos :: SourcePos 
    , lowIRMethodRetP :: Bool 
    , lowIRMethodName :: String 
    , lowIRMethodNumArgs :: Int 
    , lowIRMethodLocalsSize :: Int64
    , lowIRMethodIRGraph :: LowIRGraph }
type LowIRGraph = Graph LowBasicBlock Bool

data LowOper = OperReg RegName
             | LowOperConst Int64
             | LowOperLabel String

data MemAddr = MemAddr { memBaseReg :: RegName
                       , memDisplace :: Int
                       , memOffsetReg :: Maybe RegName
                       , memScalar :: Int } -- ^ [base + displace + offset * scalar]
             | MemAddrPtr String

data LowIRInst
    = RegBin SourcePos RegName BinOp LowOper LowOper -- ^ "r := r + r"
    | RegUn SourcePos RegName UnOp LowOper -- ^ "r := -r"
    | RegVal SourcePos RegName LowOper -- ^ "r := r"
    | RegCond
      { regCondSourcePos :: SourcePos
      , regCondDest :: RegName
      , regCondCmp :: CmpBinOp 
      , regCondCmp1 :: LowOper 
      , regCondCmp2 :: LowOper 
      , regCondSrc :: LowOper } -- ^ "r := (if r < r) r"
    | RegPush SourcePos LowOper
    | StoreMem SourcePos MemAddr LowOper
    | LoadMem SourcePos RegName MemAddr
    | LowCall SourcePos String Int -- ^ int is number of args
    | LowCallout SourcePos String Int

---
--- MidIR
---

data MidIRRepr = MidIRRepr
    { midIRFields :: [MidIRField]
    , midIRMethods :: [MidIRMethod] }
data MidIRField = MidIRField SourcePos String (Maybe Int64)
data MidIRMethod = MidIRMethod SourcePos Bool String [String] MidIRGraph
type MidIRGraph = Graph MidBasicBlock Bool

data MidOper = OperVar String
             | OperConst Int64
             | OperLabel String

data MidIRInst
    = BinAssign SourcePos String BinOp MidOper MidOper
    | UnAssign SourcePos String UnOp MidOper
    | ValAssign SourcePos String MidOper
    | CondAssign
      { condSourcePos :: SourcePos
      , condDest :: String
      , condCmp :: CmpBinOp
      , condCmp1 :: MidOper
      , condCmp2 :: MidOper
      , condSrc :: MidOper }
    | IndAssign SourcePos String MidOper
    | MidCall SourcePos (Maybe String) String [MidOper]
    | MidCallout SourcePos (Maybe String) String [Either String MidOper]

class DeadChecker a b c | a -> c where
    -- | For a given statement, returns a tuple of (unused, used)
    -- variables.  The order is 1) forget about unused, and 2) leard
    -- about used, so if a variable occurs in both unused and used, it
    -- remains used.
    checkExtents :: a -> ([c], [c])

fromMidOper :: MidOper -> [String]
fromMidOper (OperVar s) = [s]
fromMidOper _ = []

instance DeadChecker MidIRInst MidOper String where    
    checkExtents (BinAssign _ dest op oper1 oper2)
        = ([dest], fromMidOper oper1 ++ fromMidOper oper2)
    checkExtents (UnAssign _ dest op oper)
        = ([dest], fromMidOper oper)
    checkExtents (ValAssign _ dest oper)
        = ([dest], fromMidOper oper)
    checkExtents (CondAssign _ dest _ cmp1 cmp2 src)
        = ([dest], concatMap fromMidOper [cmp1, cmp2, src])
    checkExtents (IndAssign _ dest oper)
        = ([dest], fromMidOper oper)
    checkExtents (MidCall _ mdest _ opers) 
        = (maybeToList mdest, concatMap fromMidOper opers)
    checkExtents (MidCallout _ mdest _ eopers)
        = ( maybeToList mdest
          , concatMap (either (const []) fromMidOper) eopers)
          

--normalizeBlocks :: MidIRGraph -> MidIRGraph
normalizeBlocks g = rewriteGraph (cullGraph g) rules
    where rules = normalizeBlocks_rule_join_true
                  ||| normalizeBlocks_rule_join_conditional
          -- add more with `mplus`.
    
-- | Check to see if the block leading to this block unconditionally
-- goes to this block.
--normalizeBlocks_rule_join_true :: RewriteRule MidBasicBlock Bool
normalizeBlocks_rule_join_true g v
    = do let preVerts = preVertices g v
         guard $ 1 == length preVerts
         let [w] = preVerts
         guard $ v /= w -- make sure it's not a self-loop!
         case blockTest (g !!! w) of
           IRTestTrue -> guard $ hasEdgeTo g w True v
           IRTestFalse -> guard $ hasEdgeTo g w False v
           _ -> mzero
         let newblock = BasicBlock
                        { blockCode = blockCode (g !!! w) ++ blockCode (g !!! v)
                        , blockTest = blockTest (g !!! v)
                        , blockTestPos = blockTestPos (g !!! v) }
         let newouts = withStartVertex w (adjEdges g v)
         gReplace [v,w] [(w,newblock)] newouts

normalizeBlocks_rule_join_conditional g v 
    = do let preVerts = preVertices g v 
         guard $ 1 == length preVerts 
         let [w] = preVerts 
         guard $ v /= w 
         guard $ hasEdgeTo g w True v 
         guard $ hasEdgeTo g w False v 
         let newblock = BasicBlock
                        { blockCode = blockCode (g !!! w) ++ blockCode (g !!! v)
                        , blockTest = blockTest (g !!! v)
                        , blockTestPos = blockTestPos (g !!! v) }
         let newouts = withStartVertex w (adjEdges g v)
         gReplace [v,w] [(w,newblock)] newouts
             

instance Show CmpBinOp where
    show CmpLT = "<"
    show CmpGT = ">"
    show CmpLTE = "<="
    show CmpGTE = ">="
    show CmpEQ = "=="
    show CmpNEQ = "!="
    show CmpAnd = "&&"
    show CmpOr = "||"
instance Show CmpUnOp where
    show CmpZero = "0=="
    show CmpNZero = "0!="

instance Show LowOper where
    show (OperReg r) = show r
    show (LowOperConst i) = "$" ++ show i
    show (LowOperLabel s) = "$" ++ s

instance Show MemAddr where
    show (MemAddr base 0 Nothing _)
        = printf "[%s]" (show base)
    show (MemAddr base disp Nothing _)
        = printf "[%s + %s]" (show base) (show disp)
    show (MemAddr base 0 (Just offset) scalar)
        = printf "[%s + %s * %s]"
          (show base) (show offset) (show scalar)
    show (MemAddr base disp (Just offset) scalar)
        = printf "[%s + %s + %s * %s]"
          (show base) (show disp) (show offset) (show scalar)
    show (MemAddrPtr s) = "[$" ++ s ++ "]"

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

instance Show LowIRInst where
    show (RegBin pos r op oper1 oper2)
        = printf "%s := %s %s %s  {%s}"
          (show r) (show oper1) (show op) (show oper2) (showPos pos)
    show (RegUn pos r op oper)
        = printf "%s := %s %s  {%s}"
          (show r) (show op) (show oper) (showPos pos)
    show (RegVal pos r oper)
        = printf "%s := %s  {%s}"
          (show r) (show oper) (showPos pos)
    show (RegCond pos dest cmp cmp1 cmp2 src)
        = printf "%s := (if %s %s %s) %s  {%s}"
          (show dest) (show cmp1) (show cmp) (show cmp2)
          (show src) (showPos pos)
    show (RegPush pos oper)
        = printf "push %s  {%s}"
          (show oper) (showPos pos)
    show (StoreMem pos mem oper)
        = printf "%s := %s  {%s}"
          (show mem) (show oper) (showPos pos)
    show (LoadMem pos reg mem)
        = printf "%s := %s  {%s}"
          (show reg) (show mem) (showPos pos)
    show (LowCall pos name numargs)
        = printf "call %s %s  {%s}" name (show numargs) (showPos pos)
    show (LowCallout pos name numargs)
        = printf "callout %s %s  {%s}" (show name) (show numargs) (showPos pos)
          
          
instance Show MidOper where
    show (OperVar v) = v
    show (OperConst i) = "$" ++ show i
    show (OperLabel s) = "$" ++ s
          
instance Show MidIRInst where
    show (BinAssign pos r op oper1 oper2)
        = printf "%s := %s %s %s  {%s}"
          r (show oper1) (show op) (show oper2) (showPos pos)
    show (UnAssign pos r op oper)
        = printf "%s := %s %s  {%s}"
          r (show op) (show oper) (showPos pos)
    show (ValAssign pos r oper)
        = printf "%s := %s  {%s}"
          r (show oper) (showPos pos)
    show (CondAssign pos dest cmp cmp1 cmp2 src)
        = printf "%s := (if %s %s %s) %s  {%s}"
          dest (show cmp1) (show cmp) (show cmp2)
          (show src) (showPos pos)
    show (IndAssign pos dest oper)
        = printf "*%s := %s  {%s}"
          dest (show oper) (showPos pos)
    show (MidCall pos dest name args)
        = printf "%scall %s(%s)  {%s}"
          d name (intercalate ", " $ map show args) (showPos pos)
        where d = case dest of
                    Just d' -> d' ++ " := "
                    Nothing -> ""
    show (MidCallout pos dest name args)
        = printf "%scallout %s (%s)  {%s}"
          d (show name) (intercalate ", " $ map show' args) (showPos pos)
        where d = case dest of
                    Just d' -> d' ++ " := "
                    Nothing -> ""
              show' e = case e of
                          Left s -> show s
                          Right w -> show w

instance Show b => Show (IRTest b) where
  show IRTestTrue = "true"
  show IRTestFalse = "false"
  show (IRTestBinOp op oper1 oper2)
      = printf "%s %s %s"
        (show oper1) (show op) (show oper2)
  show (IRTest oper) = show oper
  show (IRTestNot oper) = "!" ++ (show oper)
  show (IRReturn Nothing) = "return"
  show (IRReturn (Just oper)) = "return " ++ (show oper)
  show (IRTestFail s) = "fail " ++ (maybe "" show s)

instance (Show a, Show b) => Show (BasicBlock a b) where
  show bb = render $ pp bb
--      = "{" ++ intercalate ", " (map show code) ++ "} (" ++ show test ++ ")"

instance (Show a, Show b) => PP (BasicBlock a b) where
  pp (BasicBlock code test pos)
      = (vcat $ map (text . show) code)
        $+$ (text $ "(" ++ show test ++ ")")
        <+> (text $ showPos pos)

--instance (Show a, Show b) => PP (LabGraph (BasicBlock a b) Bool) where
--    show (LabGraph gr l)
--        = vcat $ map (\v -> text ("L" ++ v ++ ":")
--                            $+$ (nest 3 (pp $ l v))

showPos :: SourcePos -> String
showPos pos = printf "line %i, col %i" (sourceLine pos) (sourceColumn pos)
