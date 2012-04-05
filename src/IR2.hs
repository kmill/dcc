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
    , midIRMethods :: [Method]
    , midIRGraph :: Graph MidIRInst C C }
data MidIRField = MidIRField SourcePos String (Maybe Int64)

data LowIRRepr = LowIRRepr
    { lowIRFields :: [LowIRField]
    , lowIRStrings :: [(String, SourcePos, String)]
    , lowIRMethods :: [Method]
    , lowIRGraph :: Graph LowIRInst C C }
data LowIRField = LowIRField SourcePos String Int64

type MidIRInst = Inst VarName
type LowIRInst = Inst Reg

type MidIRExpr = Expr VarName
type LowIRExpr = Expr Reg

---
--- Methods
---

-- | 'a' is the type of the metadata of the method (such as
-- arguments), and 'v' is the type of the variables
data Method = Method
    { methodPos :: SourcePos
    , methodName :: String
    , methodEntry :: Label }

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

-- | applies a function which replaces variables
mapE :: (v1 -> v2) -> Expr v1 -> Expr v2
mapE f (Lit pos x) = Lit pos x
mapE f (Var pos v) = Var pos (f v)
mapE f (LitLabel pos l) = LitLabel pos l
mapE f (Load pos exp) = Load pos (mapE f exp)
mapE f (UnOp pos op exp) = UnOp pos op (mapE f exp)
mapE f (BinOp pos op exp1 exp2) = BinOp pos op (mapE f exp1) (mapE f exp2)

---
--- Instructions
---

type SpillId = Int

data Inst v e x where
    Label      :: SourcePos -> Label                     -> Inst v C O
    Enter      :: SourcePos -> Label -> [v]              -> Inst v C O
    Store      :: SourcePos -> v -> Expr v               -> Inst v O O
    CondStore  :: SourcePos -> v -> Expr v -> Expr v     -> Inst v O O
    IndStore   :: SourcePos -> Expr v -> Expr v          -> Inst v O O
    Spill      :: SourcePos -> SpillId -> v              -> Inst v O O
    UnSpill    :: SourcePos -> v -> SpillId              -> Inst v O O
    Call       :: SourcePos -> v -> String -> [Expr v]   -> Inst v O O
    Callout    :: SourcePos -> v -> String -> [Expr v]   -> Inst v O O
    Branch     :: SourcePos -> Label                     -> Inst v O C
    CondBranch :: SourcePos -> Expr v -> Label -> Label  -> Inst v O C
    Return     :: SourcePos -> Maybe (Expr v)            -> Inst v O C
    Fail       :: SourcePos                              -> Inst v O C

instance NonLocal (Inst v) where
    entryLabel (Label _ lbl) = lbl
    entryLabel (Enter _ lbl _) = lbl
    successors (Branch _ lbl) = [lbl]
    successors (CondBranch _ exp tlbl flbl) = [tlbl, flbl]
    successors (Return _ _) = []
    successors (Fail _) = []


-- | applies a function which replaces variables
mapI :: (v1 -> v2) -> Inst v1 e x -> Inst v2 e x
mapI f (Label pos l) = Label pos l
mapI f (Enter pos l args) = Enter pos l (map f args)
mapI f (Store pos d exp) = Store pos (f d) (mapE f exp)
mapI f (CondStore pos d cexp exp) = CondStore pos (f d) (mapE f cexp) (mapE f exp)
mapI f (IndStore pos d s) = IndStore pos (mapE f d) (mapE f s)
mapI f (Spill pos id v) = Spill pos id (f v)
mapI f (UnSpill pos v id) = UnSpill pos (f v) id
mapI f (Call pos d name args) = Call pos (f d) name (map (mapE f) args)
mapI f (Callout pos d name args) = Callout pos (f d) name (map (mapE f) args)
mapI f (Branch pos l) = Branch pos l
mapI f (CondBranch pos cexp lt lf) = CondBranch pos (mapE f cexp) lt lf
mapI f (Return pos mexp) = Return pos (mexp >>= Just . (mapE f))
mapI f (Fail pos) = Fail pos

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
    showsPrec _ (Lit pos x) = shows x
    showsPrec _ (LitLabel pos lab) = showString ("$" ++ lab)
    showsPrec _ (Var pos v) = shows v
    showsPrec _ (Load pos expr) = showString "*(" . showsPrec 0 expr . showString ")"
    showsPrec p (UnOp pos op expr) = showParen (p>0) (shows op . showString " " . showsPrec 1 expr)
    showsPrec p (BinOp pos op ex1 ex2)
        = showParen (p>0) (showsPrec 1 ex1 . showString " " . shows op . showString " " . showsPrec 1 ex2)

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
    show (Enter pos lbl args)
        = printf "%s: enter %s  {%s};"
          (show lbl) (show args) (showPos pos)
    show (Store pos var expr)
        = printf "%s := %s  {%s};"
          (show var) (show expr) (showPos pos)
    show (CondStore pos var cond expr)
        = printf "%s := (if %s) %s  {%s};"
          (show var) (show cond) (show expr) (showPos pos)
    show (IndStore pos dest expr)
        = printf "*(%s) := %s  {%s};"
          (show dest) (show expr) (showPos pos)
    show (Spill pos sid var)
        = printf "spill %s <- %s  {%s};"
          (show sid) (show var) (showPos pos)
    show (UnSpill pos var sid)
        = printf "unspill %s <- %s  {%s};"
          (show var) (show sid) (showPos pos)
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

instance Show Method where
    show (Method pos name entry)
        = "method " ++ name
          ++ " goto " ++ show entry

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
    show (MidIRRepr fields strs methods graph)
        = "MidIR"
          ++ " fields\n"
          ++ unlines (map showField fields)
          ++ " strings\n"
          ++ unlines (map showStr strs)
          ++ unlines (map show methods)
          ++ showGraph show graph
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
                    ++ graphToGraphViz show (midIRGraph m)
                    ++ "}"
    where showMethod (Method pos name entry)
              = name ++ " [shape=doubleoctagon,label="++show name++"];\n"
                ++ name ++ " -> " ++ show entry ++ ";\n"
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
