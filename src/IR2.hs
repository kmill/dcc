{-# LANGUAGE GADTs, RankNTypes, TypeSynonymInstances, TypeFamilies #-}

module IR2 where

import Text.ParserCombinators.Parsec.Pos (newPos, SourcePos)

import Compiler.Hoopl
import Compiler.Hoopl.Checkpoint(CheckpointMonad(..))
import Data.Int
import Data.List
import Data.Maybe
import Text.Printf
import Text.Regex
import AST (PP, SourcePos, showPos)

bTrue, bFalse :: Int64
bTrue = -1 -- i.e. all 1's
bFalse = 0

boolToInt :: Bool -> Int64
boolToInt b = if b then bTrue else bFalse

intToBool :: Int64 -> Bool 
intToBool = (/= 0) 

-- | This is the type of the monad for working with graphs in Hoopl.
newtype GM a = GM { runGM' :: [Unique] -> [Int] -> ([Unique], [Int], a) }

class Monad m => UniqueNameMonad m where
    -- | Argument is a prefix to the unique name
    genUniqueName :: String -> m String

instance Monad GM where
    return x = GM $ \u v -> (u, v, x)
    ma >>= f = GM $ \u v -> let (u', v', a) = runGM' ma u v
                            in runGM' (f a) u' v'

instance UniqueNameMonad GM where
    genUniqueName prefix
        = GM $ \u v ->
          case v of
            (v:vs) -> (u, vs, "@" ++ prefix ++ "_" ++ show v)
            _ -> error "GM ran out of unique names! :-("

instance UniqueMonad GM where
    freshUnique = GM $ \u v ->
                  case u of
                    (u:us) -> (us, v, u)
                    _ -> error "GM ran out of Uniques! :-("

instance CheckpointMonad GM where
    type Checkpoint GM = ([Unique], [Int])
    checkpoint = GM $ \u v -> (u, v, (u, v))
    restart (u, v) = GM $ \_ _ -> (u, v, ())

runGM :: GM a -> a
runGM g = a
    where (_, _, a) = runGM' g (map intToUnique [1..]) [1..]

instance Functor GM where
    fmap f ma = do a <- ma
                   return $ f a

---
--- IRs
---

data VarName = MV String deriving (Eq, Ord)

instance Show VarName where
    show (MV s) = s
    
varToLabel :: SourcePos -> VarName -> Expr VarName
varToLabel pos (MV s) = LitLabel pos s

data MidIRRepr = MidIRRepr
    { midIRFields :: [MidIRField]
    , midIRStrings :: [(String, SourcePos, String)]
    , midIRMethods :: [Method]
    , midIRGraph :: Graph MidIRInst C C }
data MidIRField = MidIRField SourcePos String (Maybe Int64)

type MidIRInst = Inst VarName
type MidIRExpr = Expr VarName

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
              deriving (Eq, Ord)


data UnOp = OpNeg | OpNot
            deriving (Eq, Ord)
data BinOp = OpAdd | OpSub | OpMul | OpDiv | OpMod
           | CmpLT | CmpGT | CmpLTE | CmpGTE | CmpEQ | CmpNEQ
             deriving (Eq, Ord)

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

-- | 'v' is type of variables. Confused?  Look at Show (Inst v e x).
data Inst v e x where
    Label      :: SourcePos -> Label                           -> Inst v C O
    Enter      :: SourcePos -> Label -> [v]                    -> Inst v C O
    Store      :: SourcePos -> v -> Expr v                     -> Inst v O O
    -- | Semantics of (CondStore _ dest cond texp fexp) are
    -- dest := cond ? texp : fexp, with both texp and fexp
    -- being evaluated.
    CondStore  :: SourcePos -> v -> Expr v -> Expr v -> Expr v -> Inst v O O
    IndStore   :: SourcePos -> Expr v -> Expr v                -> Inst v O O
    Spill      :: SourcePos -> v                               -> Inst v O O
    Reload     :: SourcePos -> v                               -> Inst v O O
    Call       :: SourcePos -> v -> String -> [Expr v]         -> Inst v O O
    Callout    :: SourcePos -> v -> String -> [Expr v]         -> Inst v O O
    Branch     :: SourcePos -> Label                           -> Inst v O C
    CondBranch :: SourcePos -> Expr v -> Label -> Label        -> Inst v O C
    Return     :: SourcePos -> Maybe (Expr v)                  -> Inst v O C
    Fail       :: SourcePos                                    -> Inst v O C

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
mapI f (CondStore pos d cexp texp fexp) = CondStore pos (f d) (mapE f cexp) (mapE f texp) (mapE f fexp)
mapI f (IndStore pos d s) = IndStore pos (mapE f d) (mapE f s)
mapI f (Spill pos v) = Spill pos (f v)
mapI f (Reload pos v) = Reload pos (f v)
mapI f (Call pos d name args) = Call pos (f d) name (map (mapE f) args)
mapI f (Callout pos d name args) = Callout pos (f d) name (map (mapE f) args)
mapI f (Branch pos l) = Branch pos l
mapI f (CondBranch pos cexp lt lf) = CondBranch pos (mapE f cexp) lt lf
mapI f (Return pos mexp) = Return pos (mexp >>= Just . (mapE f))
mapI f (Fail pos) = Fail pos


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
        = printf "%s: enter (%s)  {%s};"
          (show lbl) (intercalate ", " (map show args)) (showPos pos)
    show (Store pos var expr)
        = printf "%s := %s  {%s};"
          (show var) (show expr) (showPos pos)
    show (CondStore pos var cond texpr fexp)
        = printf "%s := %s ? %s : %s  {%s};"
          (show var) (show cond) (show texpr) (show fexp) (showPos pos)
    show (IndStore pos dest expr)
        = printf "*(%s) := %s  {%s};"
          (show dest) (show expr) (showPos pos)
    show (Spill pos var)
        = printf "spill %s  {%s};"
          (show var) (showPos pos)
    show (Reload pos var)
        = printf "reload %s  {%s};"
          (show var) (showPos pos)
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
