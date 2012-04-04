-- | Stuff to take a hybrid AST and turn it into a MidIR

module MidIR2 where

import IR2
import Control.Monad.State
import qualified Data.Map as Map
import Data.Array
--import Text.ParserCombinators.Parsec (SourcePos)
import Text.PrettyPrint.HughesPJ
import AST
import SymbolTable
import Data.Int
import Debug.Trace
import Data.Maybe
import Data.Char
import Data.List
import Data.Graphs

---
--- Go from HAST to MidIRRepr
---

-- | This is the main entry point to the conversion.
generateMidIR :: HDProgram a -> MidIRRepr
generateMidIR prgm = programToMidIR prgm

type IREnv = [(String, (Bool, String))] -- (name, (is_field, mangled_name))

data MidIRState = MidIRState
    { genVarId :: Int
    , genStrId :: Int
    , genStrPrefix :: String
    , stringMap :: [(String, SourcePos, String)]
    }

type MidM = StateT MidIRState GM

newLocalEnvEntry :: String -> IREnv -> MidM (String, IREnv)
newLocalEnvEntry s env = do st <- get
                            let s' = "local_" ++ show (genVarId st) ++ "_" ++ s
                            put (st { genVarId = 1 + genVarId st } )
                            return (s', (s,(False, s')):env)
newLocalEnvEntries :: [String] -> IREnv -> MidM ([String], IREnv)
newLocalEnvEntries [] env = return ([], env)
newLocalEnvEntries (s:ss) env
    = do (s, env') <- newLocalEnvEntry s env
         (ss', env'') <- newLocalEnvEntries ss env'
         return (s:ss', env'')

genTmpVar :: MidM String
genTmpVar = do s <- get
               put $ s { genVarId = 1 + genVarId s }
               return $ "temp_" ++ (show $ genVarId s)

genStr :: SourcePos -> String -> MidM String
genStr pos str
    = do s <- get
         let sname = "string_"
                     ++ (genStrPrefix s)
                     ++ "_" ++ (show $ genStrId s)
         put $ s { genStrId = genStrId s + 1
                 , stringMap = (sname, pos, str):(stringMap s) }
         return sname


newGLabel :: SourcePos -> MidM (Graph (Inst v) C O)
newGLabel pos = do l <- uniqueToLabel `fmap` (lift $ freshUnique)
                   return $ gUnitCO $ Label pos lend

withBranch :: Graph (Inst v) e O -> SourcePos -> Label -> Graph (Inst v) e C
withBranch g pos l = g <*> (gUnitOC $ Branch pos l)


programToMidIR :: HDProgram a -> MidIRRepr
programToMidIR (HDProgram _ _ fields methods)
    = MidIRRepr fields' midIRmethods
      where fields' = concatMap getFields fields
            getFields (HFieldDecl _ p typ vars)
                = flip map vars $
                  (\v -> case v of
                           HPlainVar e pos tok ->
                               MidIRField pos ("field_" ++ tokenString tok) Nothing
                           HArrayVar e pos tok l ->
                               MidIRField pos ("field_" ++ tokenString tok) (Just l))
            initenv = concatMap getEnvNames fields
            getEnvNames (HFieldDecl _ p typ vars)
                = flip map vars $
                  (\v -> case v of
                           HPlainVar e pos tok -> (n, "field_" ++ n)
                               where n = tokenString tok
                           HArrayVar e pos tok l -> (n, "field_" ++ n)
                               where n = tokenString tok)
            midIRmethods = map (methodToMidIR initenv) methods

methodToMidIR :: IREnv -> HMethodDecl a -> MidIRMethod
methodToMidIR env (HMethodDecl _ pos typ tok args st)
    = MidIRMethod (tokenPos tok) returnsSomething name margs (normalizeBlocks ir)
      where name = tokenString tok
            (margs, ir) = evalState methodToMidIR' initState
            methodToMidIR' = do (sargs', env') <- newLocalEnvEntries sargs env
                                endBlock <- newBlock [] (IRReturn methReturn) pos
                                startBlock <- statementToMidIR env' endBlock no no st
                                state <- get
                                return (sargs', createGraph
                                                  (currBasicBlocks state)
                                                  (currEdges state)
                                                  startBlock)
                where no = error "continue/break used when converting to MidIR :-("
            sargs = [tokenString t | (HMethodArg _ _ t) <- args]
            initState = MidIRState
                      { genVarId = 0
                      , genBlockId = 0
                      , currBasicBlocks = []
                      , currEdges = []
                      }
            methReturn = case typ of
                           MethodVoid -> Nothing
                           _ -> Just (OperConst 0)
            returnsSomething = case typ of
                                 MethodVoid -> False
                                 _ -> True

statementToMidIR :: IREnv
                 -> Label -- ^ label on continue
                 -> Label -- ^ label on break
                 -> HStatement a -> MidM (Graph (Inst v) O O)
-- | Block
statementToMidIR env c b (HBlock _ pos vars stmts)
    = do (v', env') <- newLocalEnvEntries svars env
         stmts' <- mapM (statementToMidIR env' c b) stmts
         return $ (map init v') <*> (foldl1 (<*>) stmts')
    where svars = concatMap getSVars vars
          getSVars (HVarDecl _ pos _ toks)
              = [tokenString t | t <- toks]
          init v = gUnitOO $ Store pos v (Lit 0)
-- | If
statementToMidIR env c b (HIfSt _ pos expr cons malt)
    = do (gconsl, galtl, gend) <- replicateM 3 (newGLabel pos)
         (gexpr, expr) <- expressionToMidIR env expr
         gcons <- statementToMidIR env c b cons
         galt <- statementToMidIR env c b alt
         gif <- gUnitOC $ CondBranch pos expr (entryLabel gconsl) (entryLabel galtl)
         return $ gexpr <*> gif
                  |*><*| withBranch (gconsl <*> gcons) pos (entryLabel lend)
                  |*><*| withBranch (galtl <*> galt) pos (entryLabel lend)
                  |*><*| gend
-- | For
statementToMidIR env c b (HForSt _ pos tok exprlow exprhigh st)
    = do high <- genTmpVar
         (i, env') <- newLocalEnvEntry (tokenString tok) env
         (gcheckl, gloopl, gincrl, gendl) <- replicateM 4 (newGLabel pos)
         (glowex, lowex) <- expressionToMidIR env exprlow
         (ghighex, highex) <- expressionToMidIR env exprhigh
         loop <- statementToMidIR env' (entryLabel gincrl) (entryLabel gendl) st
         return $ (glowex <*> (gUnitOO $ Store pos i lowex)
                   <*> ghighex <*> (gUnitOO $ Store pos high highex)
                   <*> (gUnitOC $ Branch pos (entryLabel gcheckl)))
             |*><*| (gcheckl
                     <*> (gUnitOC $ CondBranch pos (BinOp pos CmpLT (Var i) (Var high))
                                      (entryLabel gloopl) (entryLabel gendl)))
             |*><*| (gloopl <*> loop
                     <*> (gUnitOC $ Branch pos (entryLabel gincrl)))
             |*><*| (gincrl
                     <*> (gUnitOO $ Store pos i (BinOp pos Add (Var i) (Lit 1)))
                     <*> (gUnitOC $ Branch pos (entryLabel gcheckl)))
             |*><*| gendl

-- | While
statementToMidIR env c b (HWhileSt _ pos expr st)
    = do t <- genTmpVar
         (gcheckl, gloopl, gendl) <- replicateM 3 (newGLabel pos)
         (gex, ex) <- expressionToMidIR env expr
         loop <- statementToMidIR env (entryLabel gcheckl) (entryLabel gendl) st
         return $ (gcheckl
                   <*> gex
                   <*> (gUnitOC $ CondBranch pos ex (entryLabel gloopl) (entryLabel gendl)))
             |*><*| (gloopl <*> loop
                     <*> gUnitOC $ Branch pos (entryLabel gcheckl))
             |*><*| gendl

-- | Return
statementToMidIR env c b (HReturnSt _ pos mexpr)
    = do dead <- newGLabel pos
         (gex, mex) <- case mexpr of
                        Just expr -> justify $ expressionToMidIR env expr
                        Nothing -> (gNil, Nothing)
         return $ gex <*> gUnitOC (Return pos mex) |*><*| dead
    where justify (gex, ex) = (gex, Just ex)

-- | Break
statementToMidIR env c b (HBreakSt _ pos)
    = do dead <- newGLabel pos
         return $ gUnitOC (Branch pos b) |*><*| dead
-- | Continue
statementToMidIR env c b (HContinueSt _ pos)
    = do dead <- newGLabel pos
         return $ gUnitOC (Branch pos b) |*><*| dead

-- | Expression
statementToMidIR env c b (HExprSt _ expr)
    = do (gex, ex) <- expressionToMidIR env expr
         return $ gex -- we ignore ex because side-effect-bearing
                      -- stuff should be in gex

makeStore pos isfield var ex
    = case isfield of
        False -> gUnitOO $ Store pos var ex
        True -> gUnitOO $ IndStore pos (LitLabel pos var) ex

-- | Assign
statementToMidIR env c b (HAssignSt senv pos loc op expr)
    = case loc of
        HPlainLocation _ pos tok ->
            let (isfield, var') = fromJust $ lookup (tokenString tok) env -- destination var
                loc' = HLoadLoc senv pos loc -- load destination var
            in do (gex, ex) <- case op of
                                 Assign -> expressionToMidIR env expr
                                 IncAssign -> handleBinaryOp env pos "+" loc' expr
                                 DecAssign -> handleBinaryOp env pos "-" loc' expr
                  return $ gex <*> makeStore pos isfield var' ex
        HArrayLocation _ pos tok iexpr ->
            let var = tokenString tok -- array var name (for error message)
                (_, var') = fromJust $ lookup var env -- destination array var
                                                      -- (and definitely a field)
                -- | it's convenient to use envLookup here since it
                -- keeps track of the length of the arrays!
                (Term _ (SArray _ len)) = fromJust $ envLookup var senv
                -- | gets the pointer to var'[i']
                arrptr i' = (BinOp pos Add
                                       (LitLabel pos var')
                                       (BinOp pos Mul (Lit pos 8) (Var pos i')))
            in do (gi, i) <- expressionToMidIR env iexpr
                  i' <- genTmpVar -- temp var for index
                  deadv <- genTmpVar
                  (gex, ex) <- expressionToMidIR env expr
                  errl <- genStr $ "Array index out of bounds at " ++ show pos ++ "\n"
                  let ex' = case op of
                              Assign -> ex
                              IncAssign -> BinOp pos Add ex (Load pos (arrptr i'))
                              DecAssign -> BinOp pos Sub (Load pos (arrptr i')) ex
                  (gcheckhighl, gokl, gfaill) <- replicateM 3 (newGLabel pos)
                  return $ ((gUnitOO $ Store pos i' i)
                            <*> (gUnitOC $ CondBranch pos (BinOp pos CmpGTE (Var pos i') 0)
                                             (entryLabel gcheckhighl) (entryLabel gfaill)))
                      |*><*| (gcheckhighl
                              <*> (gUnitOC $ CondBranch pos (BinOp pos CmpLT (Var pos i') len)
                                               (entryLabel gokl) (entryLabel gfaill)))
                      |*><*| (gfaill
                              <*> (gUnitOO $ Callout pos deadv "printf" [LitLabel errl]) -- maybe stderr?
                              <*> (gUnitOC $ Fail))
                      |*><*| (gokl <*> gex
                              <*> (gUnitOO $ IndStore pos (arrptr i') ex'))

---
--- Expressions
---
                  
handleBinaryOp :: IREnv -> SourcePos -> String -> HExpr a -> HExpr a
               -> State MidIRState (Graph (Inst v) O O, Expr v)
handleBinaryOp env pos opstr expr1 expr2
    = case opstr of
        "||" -> orExpr
        "&&" -> andExpr
        "+" -> normalExpr OpAdd
        "-" -> normalExpr OpSub
        "*" -> normalExpr OpMul
        "/" -> normalExpr OpDiv
        "%" -> normalExpr OpMod
        "==" -> normalExpr (OpCmp CmpEQ)
        "!=" -> normalExpr (OpCmp CmpNEQ)
        "<" -> normalExpr (OpCmp CmpLT)
        ">" -> normalExpr (OpCmp CmpGT)
        "<=" -> normalExpr (OpCmp CmpLTE)
        ">=" -> normalExpr (OpCmp CmpGTE)
        _ -> error "Unknown operator type in expressionToMidIR"
      where orExpr = do t <- genTmpVar
                        (gex1, ex1) <- expressionToMidIR env expr1
                        (gex2, ex2) <- expressionToMidIR env expr2
                        (ifex2l, iffalsel, donel) <- replicateM 3 (newGLabel pos)
                        let g = ((gUnitOO $ Assign pos t (Lit pos bTrue))
                                 <*> gex1 <*> (gUnitOC $ CondBranch pos ex1
                                                           (entryLabel donel) (entryLabel ifex2l)))
                              |*><*| (ifex2l <*> gex2
                                      <*> (gUnitOC $ CondBranch pos ex2
                                                       (entryLabel donel) (entryLabel iffalsel)))
                              |*><*| (iffalsel
                                      <*> (gUnitOO $ Assign pos t (Lit pos bFalse))
                                      <*> (gUnitOC $ Branch pos (entryLabel donel)))
                              |*><*| donel
                         return (g, Var pos t)
            andExpr = do t <- genTmpVar
                        (gex1, ex1) <- expressionToMidIR env expr1
                        (gex2, ex2) <- expressionToMidIR env expr2
                        (ifex2l, iftruel, donel) <- replicateM 3 (newGLabel pos)
                        let g = ((gUnitOO $ Assign pos t (Lit pos bFalse))
                                 <*> gex1 <*> (gUnitOC $ CondBranch pos ex1
                                                           (entryLabel ifex2l) (entryLabel donel)))
                              |*><*| (ifex2l <*> gex2
                                      <*> (gUnitOC $ CondBranch pos ex2
                                                       (entryLabel iftruel) (entryLabel donel)))
                              |*><*| (iftruel
                                      <*> (gUnitOO $ Assign pos t (Lit pos bTrue))
                                      <*> (gUnitOC $ Branch pos (entryLabel donel)))
                              |*><*| donel
                         return (g, Var pos t)
            normalExpr op = do (gex1, ex1) <- expressionToMidIR env expr1
                               (gex2, ex2) <- expressionToMidIR env expr2
                               return $ (gex1 <*> gex2, BinOp pos op ex1 ex2)

expressionToMidIR :: IREnv
                  -> HExpr a
                  -> State MidIRState (Graph (Inst v) O O, Expr v)
expressionToMidIR env (HBinaryOp _ pos expr1 optok expr2)
    = handleBinaryOp env pos (tokenString optok) expr1 expr2

expressionToMidIR env (HUnaryOp _ pos optok expr)
    = case tokenString optok of
        "!" -> normalExpr OpNot
        "-" -> normalExpr OpNeg
        _ -> error "Unknown unary operator :-("
    where normalExpr op = do (gex, ex) <- expressionToMidIR env expr
                             return $ (gex, UnOp pos op ex)
      
expressionToMidIR env (HExprBoolLiteral _ pos bool)
    = return (gNil, Lit pos $ boolToInt bool)
expressionToMidIR env (HExprIntLiteral _ pos i)
    = return (gNil, Lit pos $ i)
expressionToMidIR env (HExprCharLiteral _ pos c)
    = return (gNil, Lit pos $ fromIntegral $ ord c)
expressionToMidIR env (HExprStringLiteral _ pos _)
    = error "Unexpected string literal in expressionToMidIR :-("
expressionToMidIR env (HLoadLoc senv pos loc)
    = case loc of
        HPlainLocation _ pos tok ->
            let (isfield, var') = fromJust $ lookup (tokenString tok) env
            in return $ gUnitOO $ case isfield of
                                    False -> Var pos var'
                                    True -> Load pos var'
        HArrayLocation _ pos tok iexpr ->
            let var = tokenString tok -- array var name (for error message)
                (_, var') = fromJust $ lookup var env -- destination array var
                                                      -- (and definitely a field)
                -- | it's convenient to use envLookup here since it
                -- keeps track of the length of the arrays!
                (Term _ (SArray _ len)) = fromJust $ envLookup var senv
                -- | gets the pointer to var'[i']
                arrptr i' = (BinOp pos Add
                                       (LitLabel pos var')
                                       (BinOp pos Mul (Lit pos 8) (Var pos i')))
            in do (gi, i) <- expressionToMidIR env iexpr
                  i' <- genTmpVar -- temp var for index
                  deadv <- genTmpVar
                  errl <- genStr $ "Array index out of bounds at " ++ show pos ++ "\n"
                  (gcheckhighl, gokl, gfaill) <- replicateM 3 (newGLabel pos)
                  let g = ((gUnitOO $ Store pos i' i)
                           <*> (gUnitOC $ CondBranch pos (BinOp pos CmpGTE (Var i') 0)
                                            (entryLabel gcheckhighl) (entryLabel gfaill)))
                        |*><*| (gcheckhighl
                                <*> (gUnitOC $ CondBranch pos (BinOp pos CmpLT (Var i') len)
                                                 (entryLabel gokl) (entryLabel gfaill)))
                        |*><*| (gfaill
                                <*> (gUnitOO $ Callout pos deadv "printf" [LitLabel errl]) -- maybe stderr?
                                <*> (gUnitOC $ Fail))
                        |*><*| gokl
                  return (g, Load pos (arrptr i'))

expressionToMidIR env (HExprMethod _ _ call)
    = case call of
        HNormalMethod _ pos tok exprs ->
            do (gexs, exs) -> unzip `fmap` (mapM (expressionToMidIR env) exprs)
               r <- genTmpVar
               let g' = foldl (<*>) gexs -- args in right-to-left order
               return $ ( g' <*> (gUnitOO $ Call pos r (tokenString tok) exs)
                        , Var pos r )
        HCalloutMethod _ pos tok args ->
            do (gexs, exs) -> unzip `fmap` (mapM evalArg exprs)
               r <- genTmpVar
               let g' = foldl (<*>) gexs -- args in right-to-left order
               return $ ( g' <*> (gUnitOO $ Callout pos r (tokenString tok) exs)
                        , Var pos r )
            where evalArg (HCArgString _ s) = LitLabel pos `fmap` genStr s
                  evalArg (HCArgExpr _ ex) = expressionToMidIR env ex

---
--- Show MidIRRepr!
---

instance Show MidIRRepr where
  show = render . pp

instance PP MidIRRepr where
    pp m = text "MidIR"
           $+$ (nest 3 ((text "fields" $+$ (nest 3 fields))
                        $+$ (text "methods" $+$ (nest 3 methods))))
      where fields = vcat (map showField $ midIRFields m)
            showField (MidIRField pos s Nothing)
                = text s
                  <+> text ("{" ++ show pos ++ "}")
            showField (MidIRField pos s (Just l))
              = text s
                <+> text ("[" ++ show l ++ "]")
                <+> text ("{" ++ show pos ++ "}")
            methods = vcat [pp m | m <- midIRMethods m]

instance PP MidIRMethod where
    pp (MidIRMethod pos retp name args ir)
        = text ("{" ++ show pos ++ "}")
           $+$ (if retp then text "ret" else text "void") <+> text name
           <+> parens (hsep $ punctuate comma [text a | a <- args])
           $+$ (text $ "start = " ++ show (startVertex ir))
           $+$ (nest 3 (vcat [showVertex v | v <- labels ir]))
        where showVertex (i,bb) = text (show i)
                                   <+> (nest 3 (pp bb))
                                   $+$ (nest 5 (vcat (map showEdge outedges)))
                  where outedges = adjEdges ir i
                        showEdge (b,y) = text (show b ++ " -> " ++ show y)
                        

midIRToGraphViz m = "digraph name {\n"
                    ++ (showFields (midIRFields m))
                    ++ (concatMap showMethod (midIRMethods m))
                    ++ "}"
  where showMethod (MidIRMethod pos retp name args g)
            = graphToGraphVizSubgraph g (name ++ "_")
              (name ++ " [shape=doubleoctagon,label="++show mlabel++"];\n"
              ++ name ++ " -> " ++ name ++ "_" ++ show (startVertex g) ++ ";\n")
            where mlabel = (if retp then "ret " else "void ")
                           ++ name ++ " (" ++ intercalate ", " args ++ ")"
        showField (MidIRField pos name msize)
            = "{" ++ name ++ "|" ++ fromMaybe "val" (msize >>= return . show) ++ "}"
        showFields fields = "_fields_ [shape=record,label=\"fields|{"
                            ++ intercalate "|" (map showField fields)
                            ++ "}\"];\n"
