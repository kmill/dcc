{-# LANGUAGE GADTs, RankNTypes, TypeSynonymInstances, TypeFamilies #-}

module IR where

import Text.ParserCombinators.Parsec.Pos (newPos, SourcePos)

import Compiler.Hoopl
import Compiler.Hoopl.Checkpoint(CheckpointMonad(..))
import Data.Int
import Data.List
import Data.Maybe
import Text.Printf
import Text.Regex
import AST (PP, SourcePos, showPos)
import Data.Ord

bTrue, bFalse :: Int64
bTrue = 1
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
    , methodEntry :: Label
    , methodPostEntry :: Label }
    
methodByName :: String -> MidIRRepr -> Maybe Method
methodByName name midir = find (\m -> methodName m == name) $ midIRMethods midir

methodArgVars :: Method -> MidIRRepr -> [VarName]
methodArgVars method midir
    = let BodyBlock entryblock = lookupBlock (midIRGraph midir) (methodEntry method)
          entryblock :: Block MidIRInst C C
          (menter, _, _) = blockToNodeList entryblock
          enter :: MidIRInst C O
          enter = case menter of
                    JustC enter' -> enter'
      in case enter of
           Enter pos label argvars -> argvars

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
            -- | a ? b : c, evaluates both b and c
            | Cond SourcePos (Expr v) (Expr v) (Expr v)

instance Eq v => Eq (Expr v) where
    (Lit _ i1) == (Lit _ i2)  = i1 == i2
    (Var _ v1) == (Var _ v2)  = v1 == v2
    (LitLabel _ s1) == (LitLabel _ s2)  = s1 == s2
    (Load _ e1) == (Load _ e2)  = e1 == e2
    (UnOp _ op1 e1) == (UnOp _ op2 e2)
        = (op1, e1) == (op2, e2)
    (BinOp _ op1 a1 b1) == (BinOp _ op2 a2 b2)
        = (op1, a1, b1) == (op2, a2, b2)
    (Cond _ a1 b1 c1) == (Cond _ a2 b2 c2)
        = (a1, b1, c1) == (a2, b2, c2)
    _ == _ = False

instance Ord v => Ord (Expr v) where
    compare (Lit _ i1) (Lit _ i2) = compare i1 i2
    compare (Var _ v1) (Var _ v2) = compare v1 v2
    compare (LitLabel _ s1) (LitLabel _ s2)
        = compare s1 s2
    compare (Load _ e1) (Load _ e2) = compare e1 e2
    compare (UnOp _ op1 e1) (UnOp _ op2 e2)
        = compare (op1, e1) (op2, e2)
    compare (BinOp _ op1 a1 b1) (BinOp _ op2 a2 b2)
        = compare (op1, a1, b1) (op2, a2, b2)
    compare (Cond _ a1 b1 c1) (Cond _ a2 b2 c2)
        = compare (a1, b1, c1) (a2, b2, c2)
    compare Lit{} _ = LT
    compare Var{} Lit{} = GT
    compare Var{} _ = LT
    compare LitLabel{} x
        = case x of
            Lit{} -> GT
            Var{} -> GT
            _ -> LT
    compare Load{} x
        = case x of
            Lit{} -> GT
            Var{} -> GT
            LitLabel{} -> GT
            _ -> LT
    compare UnOp{} x
        = case x of
            Lit{} -> GT
            Var{} -> GT
            LitLabel{} -> GT
            Load{} -> GT
            _ -> LT
    compare BinOp{} x
        = case x of
            Lit{} -> GT
            Var{} -> GT
            LitLabel{} -> GT
            Load{} -> GT
            UnOp{} -> GT
            _ -> LT
    compare Cond{} x
        = case x of
            Lit{} -> GT
            Var{} -> GT
            LitLabel{} -> GT
            Load{} -> GT
            UnOp{} -> GT
            BinOp{} -> GT
            _ -> LT




data UnOp = OpNeg | OpNot
            deriving (Eq, Ord)
data BinOp = OpAdd | OpSub | OpMul -- | OpDiv | OpMod
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
mapE f (Cond pos expc exp1 exp2) = Cond pos (mapE f expc) (mapE f exp1) (mapE f exp2)

---
--- Instructions
---

-- | 'v' is type of variables. Confused?  Look at Show (Inst v e x).
data Inst v e x where
    Label         :: SourcePos -> Label                           -> Inst v C O
    Enter         :: SourcePos -> Label -> [v]                    -> Inst v C O
    PostEnter     :: SourcePos -> Label                           -> Inst v C O
    Store         :: SourcePos -> v -> Expr v                     -> Inst v O O
    DivStore      :: SourcePos -> v -> DivOp -> Expr v -> Expr v  -> Inst v O O
    IndStore      :: SourcePos -> Expr v -> Expr v                -> Inst v O O
    Call          :: SourcePos -> v -> String -> [Expr v]         -> Inst v O O
    Callout       :: SourcePos -> v -> String -> [Expr v]         -> Inst v O O
    -- run first label third arg times in parallel, then do second label
    Parallel      :: SourcePos -> Label -> v -> Int64 -> Label    -> Inst v O C
    -- next two should have identical semantics essentially
    ThreadReturn  :: SourcePos -> Label                           -> Inst v O C
    Branch        :: SourcePos -> Label                           -> Inst v O C
    CondBranch    :: SourcePos -> Expr v -> Label -> Label        -> Inst v O C
    -- if string is "thread" is a return from thread
    Return        :: SourcePos -> String -> Maybe (Expr v)        -> Inst v O C
    Fail          :: SourcePos                                    -> Inst v O C

data DivOp = DivQuo | DivRem
             deriving (Eq, Ord)

instance NonLocal (Inst v) where
    entryLabel (Label _ lbl) = lbl
    entryLabel (PostEnter _ lbl) = lbl
    entryLabel (Enter _ lbl _) = lbl
    successors (Parallel _ plbl _  _ elbl) = [plbl, elbl]
    successors (ThreadReturn _ lbl) = [lbl]
    successors (Branch _ lbl) = [lbl]
    successors (CondBranch _ exp tlbl flbl) = [tlbl, flbl]
    successors (Return _ _ _) = []
    successors (Fail _) = []


-- | applies a function which replaces variables
mapI :: (v1 -> v2) -> Inst v1 e x -> Inst v2 e x
mapI f (Label pos l) = Label pos l
mapI f (PostEnter pos l) = PostEnter pos l
mapI f (Enter pos l args) = Enter pos l (map f args)
mapI f (Store pos d exp) = Store pos (f d) (mapE f exp)
mapI f (DivStore pos d op exp1 exp2) = DivStore pos (f d) op
                                       (mapE f exp1) (mapE f exp2)
mapI f (IndStore pos d s) = IndStore pos (mapE f d) (mapE f s)
mapI f (Call pos d name args) = Call pos (f d) name (map (mapE f) args)
mapI f (Callout pos d name args) = Callout pos (f d) name (map (mapE f) args)
mapI f (Parallel pos plbl ivar count elbl)
    = Parallel pos plbl (f ivar) count elbl
mapI f (ThreadReturn pos l) = ThreadReturn pos l
mapI f (Branch pos l) = Branch pos l
mapI f (CondBranch pos cexp lt lf) = CondBranch pos (mapE f cexp) lt lf
mapI f (Return pos for mexp) = Return pos for (mexp >>= Just . (mapE f))
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
    showsPrec p (Cond pos exc ex1 ex2)
        = showParen (p>0) (showsPrec 1 exc
                           . showString " ? " . showsPrec 1 ex1
                           . showString " : " . showsPrec 1 ex2)

instance Show UnOp where
    show OpNeg = "negate"
    show OpNot = "not"

instance Show BinOp where
    show OpAdd = "+"
    show OpSub = "-"
    show OpMul = "*"
--    show OpDiv = "/"
--    show OpMod = "%"
    show CmpLT = "<"
    show CmpGT = ">"
    show CmpLTE = "<="
    show CmpGTE = ">="
    show CmpEQ = "=="
    show CmpNEQ = "!="

instance Show DivOp where
    show DivQuo = "/"
    show DivRem = "%"

instance Show v => Show (Inst v e x) where
    show (Label pos lbl)
        = printf "%s:  {%s};"
          (show lbl) (showPos pos)
    show (PostEnter pos lbl)
        = printf "%s:  {post enter, %s};"
          (show lbl) (showPos pos)
    show (Enter pos lbl args)
        = printf "%s: enter (%s)  {%s};"
          (show lbl) (intercalate ", " (map show args)) (showPos pos)
    show (Store pos var expr)
        = printf "%s := %s  {%s};"
          (show var) (show expr) (showPos pos)
    show (DivStore pos var op expr1 expr2)
        = printf "%s := %s %s %s  {%s};"
          (show var) (showsPrec 1 expr1 "")
          (show op) (showsPrec 1 expr2 "") (showPos pos)
    show (IndStore pos dest expr)
        = printf "*(%s) := %s  {%s};"
          (show dest) (show expr) (showPos pos)
    show (Call pos dest name args)
        = printf "%s := call %s (%s)  {%s};"
          (show dest) name (intercalate ", " $ map show args) (showPos pos)
    show (Callout pos dest name args)
        = printf "%s := callout %s (%s)  {%s};"
          (show dest) (show name) (intercalate ", " $ map show args) (showPos pos)
    show (Parallel pos plbl ivar count elbl)
        = printf "parallel (%s <- [0,..%u]) { goto %s; } goto %s; {%s};"
          (show ivar) count (show plbl) (show elbl) (showPos pos)
    show (ThreadReturn pos lbl)
        = printf "end thread to %s  {%s};"
          (show lbl) (showPos pos)
    show (Branch pos lbl)
        = printf "goto %s  {%s};"
          (show lbl) (showPos pos)
    show (CondBranch pos expr tlbl flbl)
        = printf "if %s then  {%s}\n  goto %s\nelse\n  goto %s"
          (show expr) (showPos pos) (show tlbl) (show flbl)
    show (Return pos for mexpr)
        = printf "return %s  {for %s, %s}"
          (maybe "" show mexpr) for (showPos pos)
    show (Fail pos)
        = printf "fail  {%s}"
          (showPos pos)

instance Show Method where
    show (Method pos name entry postentry)
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
    where showMethod (Method pos name entry postentry)
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
