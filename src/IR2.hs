{-# LANGUAGE GADTs, RankNTypes, TypeSynonymInstances #-}

module IR2 where

import Text.ParserCombinators.Parsec.Pos (newPos, SourcePos)

import Compiler.Hoopl
import Data.Int
import Data.List
import Data.Maybe
import Text.Printf
import Text.Regex
import AST (PP, showPos)

bTrue, bFalse :: Int64
bTrue = -1 -- i.e. all 1's
bFalse = 0

boolToInt :: Bool -> Int64
boolToInt b = if b then bTrue else bFalse

-- | This is the type of the monad for working with graphs in Hoopl.
type GM = SimpleUniqueMonad

runGM :: GM a -> a
runGM = runSimpleUniqueMonad

instance Functor GM where
    fmap f ma = do a <- ma
                   return $ f a

---
--- IRs
---

data VarName = MV String | MReg X86Reg deriving (Eq, Ord)

instance Show VarName where
    show (MV s) = s
    show (MReg r) = show r
    
varToLabel :: SourcePos -> VarName -> Expr VarName
varToLabel pos (MV s) = LitLabel pos s

data MidIRRepr = MidIRRepr
    { midIRFields :: [MidIRField]
    , midIRStrings :: [(String, SourcePos, String)]
    , midIRMethods :: [MidIRMethod] }
data MidIRField = MidIRField SourcePos String (Maybe Int64)

data LowIRRepr = LowIRRepr
    { lowIRFields :: [LowIRField]
    , lowIRStrings :: [(String, SourcePos, String)]
    , lowIRMethods :: [LowIRMethod] }
data LowIRField = LowIRField SourcePos String Int64

-- | Has a list of arguments
type MidIRMethod = Method [VarName] VarName
-- | Has the number of arguments
type LowIRMethod = Method Int Reg

type MidIRInst = Inst VarName
type LowIRInst = Inst Reg

type MidIRExpr = Expr VarName
type LowIRExpr = Expr Reg

---
--- Methods
---

-- | 'a' is the type of the metadata of the method (such as
-- arguments), and 'v' is the type of the variables
data Method a v = Method
    { methodPos :: SourcePos
    , methodName :: String
    , methodRets :: Bool -- ^ whether the method returns something
    , methodArgs :: a
    , methodEntry :: Label
    , methodBody :: Graph (Inst v) C C }

---
--- Expr
---

-- | The 'v' parameter represents the type of the variables.
data Expr v = Lit SourcePos Int64
            | Var SourcePos v
            | LitLabel SourcePos String
            | Load SourcePos (Expr v)
            | UnOp SourcePos UnOp (Expr v)
            | BinOp SourcePos BinOp (Expr v) (Expr v)


data UnOp = OpNeg | OpNot
data BinOp = OpAdd | OpSub | OpMul | OpDiv | OpMod
           | CmpLT | CmpGT | CmpLTE | CmpGTE | CmpEQ | CmpNEQ

---
--- Instructions
---

data Inst v e x where
    Label      :: SourcePos -> Label                     -> Inst v C O
    Store      :: SourcePos -> v -> Expr v               -> Inst v O O
    CondStore  :: SourcePos -> v -> Expr v -> Expr v     -> Inst v O O
    IndStore   :: SourcePos -> Expr v -> Expr v          -> Inst v O O
    Call       :: SourcePos -> v -> String -> [Expr v]   -> Inst v O O
    Callout    :: SourcePos -> v -> String -> [Expr v]   -> Inst v O O
    Branch     :: SourcePos -> Label                     -> Inst v O C
    CondBranch :: SourcePos -> Expr v -> Label -> Label  -> Inst v O C
    Return     :: SourcePos -> Maybe (Expr v)            -> Inst v O C
    Fail       :: SourcePos                              -> Inst v O C

instance NonLocal (Inst v) where
    entryLabel (Label _ lbl) = lbl
    successors (Branch _ lbl) = [lbl]
    successors (CondBranch _ exp tlbl flbl) = [tlbl, flbl]
    successors (Return _ _) = []
    successors (Fail _) = []

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

callerSaved :: [X86Reg]
callerSaved = [RAX, R10, R11]

calleeSaved :: [X86Reg]
calleeSaved = [RBP, RBX, R12, R13, R14, R15] -- should RBP be in this?

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

data Reg = RReg X86Reg
         | SReg Int
           deriving (Eq, Ord)
instance Show Reg where
    show (RReg r) = show r
    show (SReg i) = "%s" ++ show i


------------------------------------------------------------
--- Show ---------------------------------------------------
------------------------------------------------------------

instance Show v => Show (Expr v) where
    show (Lit pos x) = show x
    show (LitLabel pos lab) = "$" ++ lab
    show (Var pos v) = show v
    show (Load pos expr) = "*(" ++ show expr ++ ")"
    show (UnOp pos op expr) = show op ++ " " ++ show expr
    show (BinOp pos op ex1 ex2)
        = paren ex1 ++ " " ++ show op ++ " " ++ paren ex2
          where paren o = "(" ++ show o ++ ")"

instance Show UnOp where
    show OpNeg = "negate"
    show OpNot = "not"

instance Show BinOp where
    show OpAdd = "+"
    show OpSub = "-"
    show OpMul = "*"
    show OpDiv = "/"
    show OpMod = "%"
    show CmpLT = "<"
    show CmpGT = ">"
    show CmpLTE = "<="
    show CmpGTE = ">="
    show CmpEQ = "=="
    show CmpNEQ = "!="

instance Show v => Show (Inst v e x) where
    show (Label pos lbl)
        = printf "%s:  {%s};"
          (show lbl) (showPos pos)
    show (Store pos var expr)
        = printf "%s := %s  {%s};"
          (show var) (show expr) (showPos pos)
    show (CondStore pos var cond expr)
        = printf "%s := (if %s) %s  {%s};"
          (show var) (show cond) (show expr) (showPos pos)
    show (IndStore pos dest expr)
        = printf "*(%s) := %s  {%s};"
          (show dest) (show expr) (showPos pos)
    show (Call pos dest name args)
        = printf "%s := call %s (%s)  {%s};"
          (show dest) name (intercalate ", " $ map show args) (showPos pos)
    show (Callout pos dest name args)
        = printf "%s := callout %s (%s)  {%s};"
          (show dest) (show name) (intercalate ", " $ map show args) (showPos pos)
    show (Branch pos lbl)
        = printf "goto %s  {%s};"
          (show lbl) (showPos pos)
    show (CondBranch pos expr tlbl flbl)
        = printf "if %s then  {%s}\n  goto %s\nelse\n  goto %s"
          (show expr) (showPos pos) (show tlbl) (show flbl)
    show (Return pos mexpr)
        = printf "return %s  {%s}"
          (maybe "" show mexpr) (showPos pos)
    show (Fail pos)
        = printf "fail  {%s}"
          (showPos pos)

instance (Show a, Show v) => Show (Method a v) where
    show (Method pos name retp args entry body)
        = typ ++ " " ++ name ++ " " ++ show args ++ " {\n"
          ++ "goto " ++ show entry ++ "\n"
          ++ showGraph show body ++ "}\n"
        where typ = if retp then "ret" else "void"

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


instance Show MidIRRepr where
    show (MidIRRepr fields strs methods)
        = "MidIR"
          ++ " fields\n"
          ++ unlines (map showField fields)
          ++ " strings\n"
          ++ unlines (map showStr strs)
          ++ unlines (map show methods)
        where showField (MidIRField pos s Nothing)
                  = "  " ++ s ++ "  {" ++ showPos pos ++ "}"
              showField (MidIRField pos s (Just l))
                  = "  " ++ s ++ "[" ++ show l ++  "]  {" ++ showPos pos ++ "}"
              showStr (label, pos, string)
                  = "  " ++ label ++ " = " ++ show string ++ "  {" ++ showPos pos ++ "}"

midIRToGraphViz m = "digraph name {\n"
                    ++ (showFields (midIRFields m))
                    ++ (showStrings (midIRStrings m))
                    ++ (concatMap showMethod (midIRMethods m))
                    ++ "}"
    where showMethod (Method pos name retp args entry body)
              = graphToGraphViz show body
                ++ name ++ " [shape=doubleoctagon,label="++show mlabel++"];\n"
                ++ name ++ " -> " ++ show entry ++ ";\n"
              where mlabel = (if retp then "ret " else "void ")
                             ++ name ++ " (" ++ intercalate ", " (map show args) ++ ")"
          showField (MidIRField pos name msize)
              = "{" ++ name ++ "|" ++ fromMaybe "val" (msize >>= return . show) ++ "}"
          showFields fields = "_fields_ [shape=record,label=\"fields|{"
                              ++ intercalate "|" (map showField fields)
                              ++ "}\"];\n"
          showString (name, pos, str)
              = "{" ++ name ++ "|" ++ showPos pos ++ "|" ++ show str ++ "}"
          showStrings strings = "_strings_ [shape=record,label="
                              ++ show ("strings|{"
                                       ++ intercalate "|" (map showString strings)
                                       ++ "}")
                              ++ "];\n"

type Showing n = forall e x . n e x -> String

graphToGraphViz :: NonLocal n => Showing n -> Graph n C C -> String
graphToGraphViz node (GMany _ g_blocks _) = concatMap bviz (mapElems g_blocks)
  where bviz block = lab ++ " [shape=box, label="
                     ++ (leftAlign $ show $ b block ++ "\n") ++ "];\n"
                     ++ (concatMap (showEdge lab) (successors block))
            where lab = show $ entryLabel block
                  showEdge e x = printf "%s -> %s;\n" (show e) (show x)
                  -- | turns \n into \l so graphviz left-aligns
                  leftAlign t = subRegex (mkRegex "([^\\\\])\\\\n") t "\\1\\l"
        b block = node a ++ "\n" ++ unlines (map node bs) ++ node c
            where f :: (MaybeC C (n C O), [n O O], MaybeC C (n O C))
                    -> (n C O, [n O O], n O C)
                  f (JustC e, nodes, JustC x) = (e, nodes, x)
                  (a, bs, c) = f (blockToNodeList block)
