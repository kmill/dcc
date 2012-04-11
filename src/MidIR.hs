{-# LANGUAGE GADTs, TypeSynonymInstances #-}

-- | Stuff to take a hybrid AST and turn it into a MidIR

module MidIR where

import IR
import Compiler.Hoopl
import Control.Monad.State
import qualified Data.Map as Map
import Data.Array
--import Text.ParserCombinators.Parsec (SourcePos)
import Text.PrettyPrint.HughesPJ
import qualified AST as A
import AST(SourcePos, showPos, tokenString, tokenPos)
import SymbolTable
import Data.Int
import Debug.Trace
import Data.Maybe
import Data.Char
import Data.List
--import Data.Graphs

---
--- Go from HAST to MidIRRepr
---

-- | This is the main entry point to the conversion.  It's inside the
-- GM monad because we probably want to generate new unique labels for
-- the graph at some point later (i.e., for optimizations).
generateMidIR :: HDProgram a -> GM MidIRRepr
generateMidIR prgm = programToMidIR prgm

type IREnv = [(String, (Bool, VarName))] -- (name, (is_field, mangled_name))

data MidIRState = MidIRState
    { genStrId :: Int
    , genStrPrefix :: String
    , stringMap :: [(String, SourcePos, String)]
    }

setStrPrefix :: String -> MidM ()
setStrPrefix p = modify (\s -> s { genStrPrefix = p })

type MidM = StateT MidIRState GM

instance UniqueMonad MidM where
    freshUnique = lift freshUnique

newLocalEnvEntry :: String -> IREnv -> MidM (VarName, IREnv)
newLocalEnvEntry s env = do s' <- lift $ genUniqueName ("local_" ++ s)
                            return (MV s', (s,(False, MV s')):env)
newLocalEnvEntries :: [String] -> IREnv -> MidM ([VarName], IREnv)
newLocalEnvEntries [] env = return ([], env)
newLocalEnvEntries (s:ss) env
    = do (s, env') <- newLocalEnvEntry s env
         (ss', env'') <- newLocalEnvEntries ss env'
         return (s:ss', env'')

genTmpVar :: MidM VarName
genTmpVar = do s' <- lift $ genUniqueName "temp"
               return $ MV s'

genStr :: SourcePos -> String -> MidM String
genStr pos str
    = do s <- get
         let sname = "string_"
                     ++ (genStrPrefix s)
                     ++ "_" ++ (show $ genStrId s)
         put $ s { genStrId = genStrId s + 1
                 , stringMap = (sname, pos, str):(stringMap s) }
         return sname


withBranch :: Graph (Inst v) e O -> SourcePos -> Label -> Graph (Inst v) e C
withBranch g pos l = g <*> (mkLast $ Branch pos l)

makeStore :: SourcePos -> Bool -> VarName -> MidIRExpr -> Graph MidIRInst O O
makeStore pos isfield var ex
    = case isfield of
        False -> mkMiddle $ Store pos var ex
        True -> mkMiddle $ IndStore pos (varToLabel pos var) ex



programToMidIR :: HDProgram a -> GM MidIRRepr
programToMidIR (HDProgram _ _ fields methods)
    = do (methods', endstate) <- domethods
         let (methods, graphs) = unzip methods'
         return $ MidIRRepr fields' (stringMap endstate) methods (catGraphsCC graphs)
    where fields' = concatMap getFields fields
          getFields (HFieldDecl _ p typ vars)
              = flip map vars $
                (\v -> case v of
                         HPlainVar e pos tok ->
                             MidIRField pos ("field_" ++ tokenString tok) Nothing
                         HArrayVar e pos tok l ->
                             MidIRField pos ("field_" ++ tokenString tok) (Just l))
          initenv = map (\(k,v) -> (k, (True, MV v))) $ concatMap getEnvNames fields
          getEnvNames (HFieldDecl _ p typ vars)
              = flip map vars $
                (\v -> case v of
                         HPlainVar e pos tok -> (tokenString tok, "field_" ++ tokenString tok)
                         HArrayVar e pos tok l -> (tokenString tok, "field_" ++ tokenString tok))
          initstate = MidIRState
              { genStrId = 0
              , genStrPrefix = error "method should set this"
              , stringMap = [] }
          domethods = runStateT (mapM (methodToMidIR initenv) methods) initstate
          catGraphsCC [] = error "there should alway at least be a block for the main function"
          catGraphsCC gs = foldl1 (|*><*|) gs

methodToMidIR :: IREnv -> HMethodDecl a -> MidM (Method, Graph MidIRInst C C)
methodToMidIR env (HMethodDecl _ pos typ tok args st)
    = do setStrPrefix name
         (args', env') <- newLocalEnvEntries [tokenString t | (HMethodArg _ _ t) <- args] env
         graph <- statementToMidIR env' no no st
         startl <- freshLabel
         pl <- freshLabel
         let graph' = withBranch (mkFirst (Enter pos' startl args')) pos' pl
                      |*><*| mkFirst (PostEnter pos' pl)
                      <*> graph
                      <*> mkLast (Return pos' defret)
         return (Method (tokenPos tok) ("method_" ++ name) startl pl, graph')
    where name = (tokenString tok)
          defret = case typ of
                     A.MethodVoid -> Nothing
                     _ -> Just (Lit (tokenPos tok) 0)
          pos' = tokenPos tok
          no = error "continue/break used when converting to MidIR :-("

statementToMidIR :: IREnv
                 -> Label -- ^ label on continue
                 -> Label -- ^ label on break
                 -> HStatement a -> MidM (Graph MidIRInst O O)
-- | Block
statementToMidIR env c b (HBlock _ pos vars stmts)
    = do (v', env') <- newLocalEnvEntries svarnames env
         stmts' <- mapM (statementToMidIR env' c b) stmts
         return $ catGraphs $ map init (zip v' svarposs) ++ stmts'
    where svars = concatMap getSVars vars
          getSVars (HVarDecl _ pos _ toks)
              = [(tokenString t, pos) | t <- toks]
          (svarnames, svarposs) = unzip svars
          init (v, pos) = mkMiddle $ Store pos v (Lit pos 0)
-- | If
statementToMidIR env c b (HIfSt _ pos expr cons malt)
    = do [consl, altl, endl] <- replicateM 3 freshLabel
         (gexpr, expr) <- expressionToMidIR env expr
         gcons <- statementToMidIR env c b cons
         galt <- case malt of
                   Just alt -> statementToMidIR env c b alt
                   Nothing -> return GNil
         return $ gexpr <*> (mkLast $ CondBranch pos expr consl altl)
                  |*><*| withBranch (mkFirst (Label pos consl) <*> gcons) pos endl
                  |*><*| withBranch (mkFirst (Label pos altl) <*> galt) pos endl
                  |*><*| mkFirst (Label pos endl)
-- | For
statementToMidIR env c b (HForSt _ pos tok exprlow exprhigh st)
    = do high <- genTmpVar
         (i, env') <- newLocalEnvEntry (tokenString tok) env
         [checkl, loopl, incrl, endl] <- replicateM 4 freshLabel
         (glowex, lowex) <- expressionToMidIR env exprlow
         (ghighex, highex) <- expressionToMidIR env exprhigh
         loop <- statementToMidIR env' incrl endl st
         return $ (glowex <*> (mkMiddle $ Store pos i lowex)
                   <*> ghighex <*> (mkMiddle $ Store pos high highex)
                   <*> (mkLast $ Branch pos checkl))
             |*><*| (mkFirst (Label pos checkl)
                     <*> (mkLast $ CondBranch pos (BinOp pos CmpLT (Var pos i) (Var pos high))
                                      loopl endl))
             |*><*| (mkFirst (Label pos loopl) <*> loop
                     <*> (mkLast $ Branch pos incrl))
             |*><*| (mkFirst (Label pos incrl)
                     <*> (mkMiddle $ Store pos i (BinOp pos OpAdd (Var pos i) (Lit pos 1)))
                     <*> (mkLast $ Branch pos checkl))
             |*><*| mkFirst (Label pos endl)

-- | While
statementToMidIR env c b (HWhileSt _ pos expr st)
    = do t <- genTmpVar
         [checkl, loopl, endl] <- replicateM 3 freshLabel
         (gex, ex) <- expressionToMidIR env expr
         loop <- statementToMidIR env checkl endl st
         return $ (mkLast $ Branch pos checkl)
             |*><*| (mkFirst (Label pos checkl)
                   <*> gex
                   <*> (mkLast $ CondBranch pos ex loopl endl))
             |*><*| (mkFirst (Label pos loopl) <*> loop
                     <*> (mkLast $ Branch pos checkl))
             |*><*| mkFirst (Label pos endl)

-- | Return
statementToMidIR env c b (HReturnSt _ pos mexpr)
    = do dead <- freshLabel
         (gex, mex) <- case mexpr of
                        Just expr -> justify `fmap` expressionToMidIR env expr
                        Nothing -> return (GNil, Nothing)
         return $ gex <*> mkLast (Return pos mex) |*><*| mkFirst (Label pos dead)
    where justify (gex, ex) = (gex, Just ex)

-- | Break
statementToMidIR env c b (HBreakSt _ pos)
    = do dead <- freshLabel
         return $ mkLast (Branch pos b) |*><*| mkFirst (Label pos dead)
-- | Continue
statementToMidIR env c b (HContinueSt _ pos)
    = do dead <- freshLabel
         return $ mkLast (Branch pos b) |*><*| mkFirst (Label pos dead)

-- | Expression
statementToMidIR env c b (HExprSt _ expr)
    = do (gex, ex) <- expressionToMidIR env expr
         return $ gex -- we ignore ex because side-effect-bearing
                      -- stuff should be in gex

-- | Assign
statementToMidIR env c b (HAssignSt senv pos loc op expr)
    = case loc of
        HPlainLocation _ pos tok ->
            let (isfield, var') = fromJust $ lookup (tokenString tok) env -- destination var
                loc' = HLoadLoc senv pos loc -- load destination var
            in do (gex, ex) <- case op of
                                 A.Assign -> expressionToMidIR env expr
                                 A.IncAssign -> handleBinaryOp env pos "+" loc' expr
                                 A.DecAssign -> handleBinaryOp env pos "-" loc' expr
                  return $ gex <*> makeStore pos isfield var' ex
        HArrayLocation _ pos tok iexpr ->
            let var = tokenString tok -- array var name (for error message)
                (_, var') = fromJust $ lookup var env -- destination array var
                                                      -- (and definitely a field)
                -- | it's convenient to use envLookup here since it
                -- keeps track of the length of the arrays!
                (Term _ (SArray _ len)) = fromJust $ envLookup var senv
                -- | gets the pointer to var'[i']
                arrptr i' = (BinOp pos OpAdd
                                       (varToLabel pos var')
                                       (BinOp pos OpMul (Var pos i') (Lit pos 8)))
            in do (gi, i) <- expressionToMidIR env iexpr
                  i' <- genTmpVar -- temp var for index
                  deadv <- genTmpVar
                  (gex, ex) <- expressionToMidIR env expr
                  errl <- genStr pos $ "Array index out of bounds at " ++ show pos ++ "\n"
                  let ex' = case op of
                              A.Assign -> ex
                              A.IncAssign -> BinOp pos OpAdd (Load pos (arrptr i')) ex
                              A.DecAssign -> BinOp pos OpSub (Load pos (arrptr i')) ex
                  [checkhighl, okl, faill] <- replicateM 3 freshLabel
                  return $ ((mkMiddle $ Store pos i' i)
                            <*> (mkLast $ CondBranch pos (BinOp pos CmpGTE (Var pos i') (Lit pos 0))
                                             checkhighl faill))
                      |*><*| (mkFirst (Label pos checkhighl)
                              <*> (mkLast $ CondBranch pos (BinOp pos CmpLT (Var pos i') (Lit pos len))
                                               okl faill))
                      |*><*| (mkFirst (Label pos faill)
                              <*> (mkMiddle $ Callout pos deadv "printf" [LitLabel pos errl]) -- maybe stderr?
                              <*> (mkLast $ Fail pos))
                      |*><*| (mkFirst (Label pos okl) <*> gex
                              <*> (mkMiddle $ IndStore pos (arrptr i') ex'))

---
--- Expressions
---
                  
handleBinaryOp :: IREnv -> SourcePos -> String -> HExpr a -> HExpr a
               -> MidM (Graph MidIRInst O O, MidIRExpr)
handleBinaryOp env pos opstr expr1 expr2
    = case opstr of
        "||" -> orExpr
        "&&" -> andExpr
        "+" -> normalExpr OpAdd
        "-" -> normalExpr OpSub
        "*" -> normalExpr OpMul
        "/" -> normalExpr OpDiv
        "%" -> normalExpr OpMod
        "==" -> normalExpr CmpEQ
        "!=" -> normalExpr CmpNEQ
        "<" -> normalExpr CmpLT
        ">" -> normalExpr CmpGT
        "<=" -> normalExpr CmpLTE
        ">=" -> normalExpr CmpGTE
        _ -> error "Unknown operator type in expressionToMidIR"
      where orExpr = do t <- genTmpVar
                        (gex1, ex1) <- expressionToMidIR env expr1
                        (gex2, ex2) <- expressionToMidIR env expr2
                        [ifex2l, iffalsel, donel] <- replicateM 3 freshLabel
                        let g = ((mkMiddle $ Store pos t (Lit pos bTrue))
                                 <*> gex1 <*> (mkLast $ CondBranch pos ex1 donel ifex2l))
                              |*><*| (mkFirst (Label pos ifex2l) <*> gex2
                                      <*> (mkLast $ CondBranch pos ex2 donel iffalsel))
                              |*><*| (mkFirst (Label pos iffalsel)
                                      <*> (mkMiddle $ Store pos t (Lit pos bFalse))
                                      <*> (mkLast $ Branch pos donel))
                              |*><*| mkFirst (Label pos donel)
                        return (g, Var pos t)
            andExpr = do t <- genTmpVar
                         (gex1, ex1) <- expressionToMidIR env expr1
                         (gex2, ex2) <- expressionToMidIR env expr2
                         [ifex2l, iftruel, donel] <- replicateM 3 freshLabel
                         let g = ((mkMiddle $ Store pos t (Lit pos bFalse))
                                  <*> gex1 <*> (mkLast $ CondBranch pos ex1 ifex2l donel))
                               |*><*| (mkFirst (Label pos ifex2l) <*> gex2
                                       <*> (mkLast $ CondBranch pos ex2 iftruel donel))
                               |*><*| (mkFirst (Label pos iftruel)
                                       <*> (mkMiddle $ Store pos t (Lit pos bTrue))
                                       <*> (mkLast $ Branch pos donel))
                               |*><*| mkFirst (Label pos donel)
                         return (g, Var pos t)
            normalExpr op = do (gex1, ex1) <- expressionToMidIR env expr1
                               (gex2, ex2) <- expressionToMidIR env expr2
                               return $ (gex1 <*> gex2, BinOp pos op ex1 ex2)

expressionToMidIR :: IREnv
                  -> HExpr a
                  -> MidM (Graph MidIRInst O O, MidIRExpr)
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
    = return (GNil, Lit pos $ boolToInt bool)
expressionToMidIR env (HExprIntLiteral _ pos i)
    = return (GNil, Lit pos $ i)
expressionToMidIR env (HExprCharLiteral _ pos c)
    = return (GNil, Lit pos $ fromIntegral $ ord c)
expressionToMidIR env (HExprStringLiteral _ pos _)
    = error "Unexpected string literal in expressionToMidIR :-("
expressionToMidIR env (HLoadLoc senv pos loc)
    = case loc of
        HPlainLocation _ pos tok ->
            let (isfield, var') = fromJust $ lookup (tokenString tok) env
            in return (GNil, case isfield of
                               False -> Var pos var'
                               True -> Load pos (varToLabel pos var'))
        HArrayLocation _ pos tok iexpr ->
            let var = tokenString tok -- array var name (for error message)
                (_, var') = fromJust $ lookup var env -- destination array var
                                                      -- (and definitely a field)
                -- | it's convenient to use envLookup here since it
                -- keeps track of the length of the arrays!
                (Term _ (SArray _ len)) = fromJust $ envLookup var senv
                -- | gets the pointer to var'[i']
                arrptr i' = (BinOp pos OpAdd
                                       (varToLabel pos var')
                                       (BinOp pos OpMul (Lit pos 8) (Var pos i')))
            in do (gi, i) <- expressionToMidIR env iexpr
                  i' <- genTmpVar -- temp var for index
                  deadv <- genTmpVar
                  errl <- genStr pos $ "Array index out of bounds at " ++ show pos ++ "\n"
                  [checkhighl, okl, faill] <- replicateM 3 freshLabel
                  let g = ((mkMiddle $ Store pos i' i)
                           <*> (mkLast $ CondBranch pos (BinOp pos CmpGTE (Var pos i') (Lit pos 0))
                                            checkhighl faill))
                        |*><*| (mkFirst (Label pos checkhighl)
                                <*> (mkLast $ CondBranch pos (BinOp pos CmpLT (Var pos i') (Lit pos len))
                                                 okl faill))
                        |*><*| (mkFirst (Label pos faill)
                                <*> (mkMiddle $ Callout pos deadv "printf" [LitLabel pos errl]) -- maybe stderr?
                                <*> (mkLast $ Fail pos))
                        |*><*| mkFirst (Label pos okl)
                  return (g, Load pos (arrptr i'))

expressionToMidIR env (HExprMethod _ _ call)
    = case call of
        HNormalMethod _ pos tok exprs ->
            do (gexs, exs) <- unzip `fmap` (mapM (expressionToMidIR env) exprs)
               let g' = catGraphs gexs -- args in right-to-left order
               temp <- genTmpVar
               return $ ( g' <*> (mkMiddle $ Call pos temp ("method_" ++ tokenString tok) exs)
                        , Var pos temp)
        HCalloutMethod _ pos tok args ->
            do (gexs, exs) <- unzip `fmap` (mapM evalArg args)
               let g' = catGraphs gexs -- args in right-to-left order
               temp <- genTmpVar
               return $ ( g' <*> (mkMiddle $ Callout pos temp (tokenString tok) exs)
                        , Var pos temp )
            where evalArg (HCArgString _ s)
                      = (\e -> (GNil, LitLabel pos e)) `fmap` genStr pos (tokenString s)
                  evalArg (HCArgExpr _ ex)
                      = expressionToMidIR env ex

---
--- Show MidIRRepr!
---

-- instance Show MidIRRepr where
--   show = render . pp



-- instance PP MidIRRepr where
--     pp m = text "MidIR"
--            $+$ (nest 3 ((text "fields" $+$ (nest 3 fields))
--                         $+$ (text "methods" $+$ (nest 3 methods))))
--       where fields = vcat (map showField $ midIRFields m)
--             showField (MidIRField pos s Nothing)
--                 = text s
--                   <+> text ("{" ++ show pos ++ "}")
--             showField (MidIRField pos s (Just l))
--               = text s
--                 <+> text ("[" ++ show l ++ "]")
--                 <+> text ("{" ++ show pos ++ "}")
--             methods = vcat [pp m | m <- midIRMethods m]

-- instance PP MidIRMethod where
--     pp (MidIRMethod pos retp name args ir)
--         = text ("{" ++ show pos ++ "}")
--            $+$ (if retp then text "ret" else text "void") <+> text name
--            <+> parens (hsep $ punctuate comma [text a | a <- args])
--            $+$ (text $ "start = " ++ show (startVertex ir))
--            $+$ (nest 3 (vcat [showVertex v | v <- labels ir]))
--         where showVertex (i,bb) = text (show i)
--                                    <+> (nest 3 (pp bb))
--                                    $+$ (nest 5 (vcat (map showEdge outedges)))
--                   where outedges = adjEdges ir i
--                         showEdge (b,y) = text (show b ++ " -> " ++ show y)
                        

-- midIRToGraphViz m = "digraph name {\n"
--                     ++ (showFields (midIRFields m))
--                     ++ (concatMap showMethod (midIRMethods m))
--                     ++ "}"
--   where showMethod (MidIRMethod pos retp name args g)
--             = graphToGraphVizSubgraph g (name ++ "_")
--               (name ++ " [shape=doubleoctagon,label="++show mlabel++"];\n"
--               ++ name ++ " -> " ++ name ++ "_" ++ show (startVertex g) ++ ";\n")
--             where mlabel = (if retp then "ret " else "void ")
--                            ++ name ++ " (" ++ intercalate ", " args ++ ")"
--         showField (MidIRField pos name msize)
--             = "{" ++ name ++ "|" ++ fromMaybe "val" (msize >>= return . show) ++ "}"
--         showFields fields = "_fields_ [shape=record,label=\"fields|{"
--                             ++ intercalate "|" (map showField fields)
--                             ++ "}\"];\n"
