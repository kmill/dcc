-- | Stuff to take a hybrid AST and turn it into a MidIR

module MidIR where

import IR
import Control.Monad.State
import qualified Data.Map as Map
import Data.Array
import Text.ParserCombinators.Parsec (SourcePos)
import Text.PrettyPrint.HughesPJ
import AST
import SymbolTable
import Data.Int
import Debug.Trace
import IR
import Data.Maybe
import Data.Char
import Data.List
import Data.Graphs

data MidIRField = MidIRField SourcePos String (Maybe Int64)
data MidIRMethod = MidIRMethod SourcePos String [String] MidIRGraph

type MidIRGraph = Graph MidBasicBlock Bool

data MidIRRepr = MidIRRepr
    { midIRFields :: [MidIRField]
    , midIRMethods :: [MidIRMethod] }

generateMidIR :: HDProgram a -> MidIRRepr
generateMidIR prgm = programToMidIR prgm

type IREnv = [(String, String)]

data MidIRState = MidIRState
    { genVarId :: Int
    , genBlockId :: Int
    , currBasicBlocks :: [(Int, MidBasicBlock)]
    , currEdges :: [(Int, Bool, Int)]
    }

newLocalEnvEntry :: String -> IREnv -> State MidIRState (String, IREnv)
newLocalEnvEntry s env = do st <- get
                            let s' = "local_" ++ show (genVarId st) ++ "_" ++ s
                            put (st { genVarId = 1 + genVarId st } )
                            return (s', (s,s'):env)
newLocalEnvEntries :: [String] -> IREnv -> State MidIRState ([String], IREnv)
newLocalEnvEntries [] env = return ([], env)
newLocalEnvEntries (s:ss) env
    = do (s, env') <- newLocalEnvEntry s env
         (ss', env'') <- newLocalEnvEntries ss env'
         return (s:ss', env'')

genTmpVar :: State MidIRState String
genTmpVar = do s <- get
               put $ s { genVarId = 1 + genVarId s }
               return $ "temp_" ++ (show $ genVarId s)

addEdge :: Int -> Bool -> Int -> State MidIRState ()
addEdge start b end = do s <- get
                         put $ s { currEdges = (start,b,end) : (currEdges s) }

newBlock :: [MidIRInst] -> IRTest MidOper -> State MidIRState Int
newBlock code test = do id <- genBlockID
                        newBlockWithId id code test

genBlockID :: State MidIRState Int
genBlockID = do s <- get
                put $ s { genBlockId = 1 + genBlockId s }
                return $ genBlockId s

newBlockWithId :: Int -> [MidIRInst] -> IRTest MidOper -> State MidIRState Int
newBlockWithId id code test
  = do s <- get
       let block = BasicBlock code test
       put $ s { currBasicBlocks = (id,block):(currBasicBlocks s) }
       return id

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
methodToMidIR env (HMethodDecl _ _ typ tok args st)
    = MidIRMethod (tokenPos tok) name margs (normalizeBlocks ir)
      where name = tokenString tok
            (margs, ir) = evalState methodToMidIR' initState
            methodToMidIR' = do (sargs', env') <- newLocalEnvEntries sargs env
                                endBlock <- newBlock [] (IRReturn methReturn)
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

statementToMidIR :: IREnv
                 -> Int -- ^ BasicBlock on success
                 -> Int -- ^ BasicBlock on continue
                 -> Int -- ^ BasicBlock on break
                 -> HStatement a -> State MidIRState Int
-- | Block
statementToMidIR env s c b (HBlock _ _ vars stmts)
    = do (v', env') <- newLocalEnvEntries svars env
         let stmnts' = [\s' -> statementToMidIR env' s' c b st | st <- stmts]
         foldr (=<<) (return s) stmnts'
    where svars = concatMap getSVars vars
          getSVars (HVarDecl _ pos _ toks)
              = [tokenString t | t <- toks]
-- | If
statementToMidIR env s c b (HIfSt _ pos expr cons malt)
    = do cons' <- statementToMidIR env s c b cons
         alt' <- case malt of
                   Just alt -> statementToMidIR env s c b alt
                   Nothing -> return s
         tvar <- genTmpVar
         block <- newBlock [] (IRTest (OperVar tvar))
         addEdge block True cons'
         addEdge block False alt'
         e <- expressionToMidIR env block tvar expr
         return e
-- | For
statementToMidIR env s c b (HForSt _ pos tok exprlow exprhigh st)
    = do low <- genTmpVar
         high <- genTmpVar
         (s', env') <- newLocalEnvEntry (tokenString tok) env
         --    doLow
         --    doHigh
         --    initBlock (enter new env, too)
         -- L: checkBlock
         --    if true : continue; else : goto E
         --    stblock
         --    incrBlock
         --    goto L
         -- E:
         initBlock <- newBlock [ValAssign (tokenPos tok) s' (OperVar low)]
                      IRTestTrue
         checkBlock <- newBlock []
                       (IRTestBinOp CmpLTE (OperVar s') (OperVar high))
         addEdge initBlock True checkBlock
         addEdge checkBlock False s
         incrBlock <- newBlock [BinAssign pos s' OpAdd (OperVar s') (OperConst 1)]
                      IRTestTrue
         addEdge incrBlock True checkBlock
         stblock <- statementToMidIR env' incrBlock incrBlock s st
         addEdge checkBlock True stblock
         doHigh <- expressionToMidIR env initBlock high exprhigh
         doLow <- expressionToMidIR env doHigh low exprlow
         return doLow

-- | While
statementToMidIR env s c b (HWhileSt _ pos expr st)
    = do t <- genTmpVar
         checkBlock <- newBlock []
                       (IRTest (OperVar t))
         evalExpr <- expressionToMidIR env checkBlock t expr
         stblock <- statementToMidIR env evalExpr evalExpr s st
         addEdge checkBlock True stblock
         addEdge checkBlock False s
         return evalExpr
-- | Return
statementToMidIR env s c b (HReturnSt _ pos Nothing)
    = newBlock [] (IRReturn Nothing)
statementToMidIR env s c b (HReturnSt _ pos (Just expr))
    = do t <- genTmpVar
         ret <- newBlock [] (IRReturn $ Just (OperVar t))
         exprBlock <- expressionToMidIR env ret t expr
         return exprBlock
-- | Break
statementToMidIR env s c b (HBreakSt _ pos)         
    = return b
-- | Continue
statementToMidIR env s c b (HContinueSt _ pos)
    = return c
-- | Expression
statementToMidIR env s c b (HExprSt _ expr)
    = do t <- genTmpVar
         expressionToMidIR env s t expr
-- | Assign
statementToMidIR env s c b (HAssignSt senv pos loc op expr)
    = case loc of
        HPlainLocation _ pos tok ->
            let var' = fromJust $ lookup (tokenString tok) env
            in expressionToMidIR env s var' expr
        HArrayLocation _ pos tok iexpr ->
            let var = tokenString tok
                var' = fromJust $ lookup var env
                -- | it's convenient to use envLookup here since it
                -- keeps track of the length of the arrays!
                (Term _ (SArray _ len)) = fromJust $ envLookup var senv
            in do ts <- genTmpVar
                  td <- genTmpVar
                  ti <- genTmpVar
                  storeBlock <- newBlock [ BinAssign pos ti OpMul
                                            (OperVar ti) (OperConst 8)
                                         , BinAssign pos td OpAdd
                                           (OperVar var') (OperVar ti)
                                         , IndAssign pos td (OperVar ts)]
                                IRTestTrue
                  addEdge storeBlock True s
                  evalexpr <- expressionToMidIR env storeBlock ts expr
                  failBounds <- newBlock []
                                (IRTestFail ("Array index out of bounds at "
                                             ++ show pos))
                  checkBounds2 <- newBlock []
                                  (IRTestBinOp CmpGTE (OperVar ti) (OperConst 0))
                  addEdge checkBounds2 False failBounds
                  addEdge checkBounds2 True evalexpr
                  checkBounds <- newBlock []
                                 (IRTestBinOp CmpLT (OperVar ti) (OperConst len))
                  addEdge checkBounds False failBounds
                  addEdge checkBounds True checkBounds2
                  evaliexpr <- expressionToMidIR env checkBounds ti iexpr
                  return evaliexpr


---
--- Expressions
---

expressionToMidIR :: IREnv
                  -> Int -- ^ BasicBlock on success
                  -> String -- ^ variable to output to
                  -> HExpr a -> State MidIRState Int
expressionToMidIR env s out (HBinaryOp _ pos expr1 optok expr2)
    = case tokenString optok of
        "||" -> orExpr
        "&&" -> andExpr
        "+" -> normalExpr OpAdd
        "-" -> normalExpr OpSub
        "*" -> normalExpr OpMul
        "/" -> normalExpr OpDiv
        "%" -> normalExpr OpMod
        "==" -> normalExpr (OpBinCmp CmpEQ)
        "!=" -> normalExpr (OpBinCmp CmpNEQ)
        "<" -> normalExpr (OpBinCmp CmpLT)
        ">" -> normalExpr (OpBinCmp CmpGT)
        "<=" -> normalExpr (OpBinCmp CmpLTE)
        ">=" -> normalExpr (OpBinCmp CmpGTE)
        _ -> error "Unknown operator type in expressionToMidIR"
      where orExpr = do trueBlock <- newBlock [ValAssign pos out
                                               (OperConst $ boolToInt True)]
                                     IRTestTrue
                        addEdge trueBlock True s
                        t <- genTmpVar
                        shortCircuit <- newBlock []
                                        (IRTest (OperVar t))
                        expr1Block <- expressionToMidIR env shortCircuit t expr1
                        expr2Block <- expressionToMidIR env s out expr2
                        addEdge shortCircuit True trueBlock
                        addEdge shortCircuit False expr2Block
                        return expr1Block
            andExpr = do falseBlock <- newBlock [ValAssign pos out
                                                 (OperConst $ boolToInt False)]
                                       IRTestTrue
                         addEdge falseBlock True s
                         t <- genTmpVar
                         shortCircuit <- newBlock []
                                         (IRTest (OperVar t))
                         expr1Block <- expressionToMidIR env shortCircuit t expr1
                         expr2Block <- expressionToMidIR env s out expr2
                         addEdge shortCircuit False falseBlock
                         addEdge shortCircuit True expr2Block
                         return expr1Block
            normalExpr op = do t1 <- genTmpVar
                               t2 <- genTmpVar
                               opBlock <- newBlock
                                          [BinAssign pos out op
                                                     (OperVar t1) (OperVar t2)]
                                          IRTestTrue
                               addEdge opBlock True s
                               expr2Block <- expressionToMidIR env opBlock t2 expr2
                               expr1Block <- expressionToMidIR env expr2Block t1 expr1
                               return expr1Block
expressionToMidIR env s out (HUnaryOp _ pos optok expr)
    = case tokenString optok of
        "!" -> normalExpr OpNot
        "-" -> normalExpr OpNeg
    where normalExpr op = do opBlock <- newBlock [UnAssign pos out op (OperVar out)]
                                        IRTestTrue
                             addEdge opBlock True s
                             expressionToMidIR env opBlock out expr
      
expressionToMidIR env s out (HExprBoolLiteral _ pos bool)
    = do block <- newBlock
                  [ValAssign pos out (OperConst $ boolToInt bool)]
                  IRTestTrue
         addEdge block True s
         return block
expressionToMidIR env s out (HExprIntLiteral _ pos i)
    = do block <- newBlock
                  [ValAssign pos out (OperConst i)]
                  IRTestTrue
         addEdge block True s
         return block
expressionToMidIR env s out (HExprCharLiteral _ pos c)
    = do block <- newBlock
                  [ValAssign pos out (OperConst $ fromIntegral $ ord c)]
                  IRTestTrue
         addEdge block True s
         return block
expressionToMidIR env s out (HExprStringLiteral _ pos _)
    = error "Unexpected string literal in expressionToMidIR :-("
expressionToMidIR env s out (HLoadLoc senv pos loc)
    = case loc of
        HPlainLocation _ pos tok ->
            let var' = fromJust $ lookup (tokenString tok) env
            in do assblock <- newBlock [ValAssign pos out (OperVar var')]
                              IRTestTrue
                  addEdge assblock True s
                  return assblock
        HArrayLocation _ pos tok iexpr ->
            let var = tokenString tok
                var' = fromJust $ lookup var env
                -- | it's convenient to use envLookup here since it
                -- keeps track of the length of the arrays!
                (Term _ (SArray _ len)) = fromJust $ envLookup var senv
            in do ts <- genTmpVar
                  ti <- genTmpVar
                  loadBlock <- newBlock [ UnAssign pos ts OpAddr (OperVar var')
                                        , BinAssign pos ti OpMul
                                            (OperVar ti) (OperConst 8)
                                         , BinAssign pos ts OpAdd
                                           (OperVar ts) (OperVar ti)
                                         , UnAssign pos out OpDeref (OperVar ts)]
                               IRTestTrue
                  addEdge loadBlock True s
                  failBounds <- newBlock []
                                (IRTestFail ("Array index out of bounds at "
                                             ++ show pos))
                  checkBounds2 <- newBlock []
                                  (IRTestBinOp CmpGTE (OperVar ti) (OperConst 0))
                  addEdge checkBounds2 False failBounds
                  addEdge checkBounds2 True loadBlock
                  checkBounds <- newBlock []
                                 (IRTestBinOp CmpLT (OperVar ti) (OperConst len))
                  addEdge checkBounds False failBounds
                  addEdge checkBounds True checkBounds2
                  evaliexpr <- expressionToMidIR env checkBounds ti iexpr
                  return evaliexpr
expressionToMidIR env s out (HExprMethod _ _ call)
    = case call of
        HNormalMethod _ pos tok exprs ->
            do tmps <- replicateM (length exprs) genTmpVar
               callFunction <- newBlock [MidCall pos (Just out) (tokenString tok)
                                         (map OperVar tmps)]
                               IRTestTrue
               addEdge callFunction True s
               evalArgs <- foldr (=<<) (return callFunction)
                           [(\s' -> expressionToMidIR env s' t e)
                            | (t,e) <- zip tmps exprs]
               return evalArgs
        HCalloutMethod _ pos tok args ->
            do tmps <- mapM arg' args
               callFunction <- newBlock [MidCallout pos (Just out) (tokenString tok)
                                         (map arg'' tmps)]
                               IRTestTrue
               addEdge callFunction True s
               evalArgs <- foldr (=<<) (return callFunction)
                           [evalArg t a | (t,a) <- zip tmps args]
               return evalArgs
            where arg' (HCArgString _ s) = return $ Left (tokenString s)
                  arg' (HCArgExpr _ expr) = do t <- genTmpVar
                                               return $ Right t
                  evalArg t (HCArgString _ str) s' = return s'
                  evalArg (Right t) (HCArgExpr _ expr) s' = expressionToMidIR env s' t expr
                  arg'' (Left s) = Left s
                  arg'' (Right t) = Right $ OperVar t

normalizeBlocks_rule_join_true:: RewriteRule MidBasicBlock Bool
normalizeBlocks_rule_join_true g v
    = do let preVerts = preVertices g v
         guard $ 1 == length preVerts
         let [w] = preVerts
         guard $ v /= w
         guard $ checkIsTrue $ blockTest (g !!! w)
         let newblock = BasicBlock
                        { blockCode = blockCode (g !!! w) ++ blockCode (g !!! v)
                        , blockTest = blockTest (g !!! v) }
         let newouts = withStartVertex w (adjEdges g v)
         gReplace [v,w] [(w,newblock)] newouts
    where checkIsTrue IRTestTrue = True
          checkIsTrue _ = False

normalizeBlocks :: MidIRGraph -> MidIRGraph
normalizeBlocks g = rewriteGraph g rules
    where rules = normalizeBlocks_rule_join_true

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
    pp (MidIRMethod pos name args ir)
        = text ("{" ++ show pos ++ "}")
           $+$ text name
           <+> parens (hsep $ punctuate comma [text a | a <- args])
           $+$ (text $ "start = " ++ show (startVertex ir))
           $+$ (nest 3 (vcat [showVertex v | v <- labels ir]))
        where showVertex (i,bb) = text (show i)
                                   <+> (nest 3 (pp bb))
                                   $+$ (nest 5 (vcat (map showEdge outedges)))
                  where outedges = adjEdges ir i
                        showEdge (b,y) = text (show b ++ " -> " ++ show y)
                        

midIRToGraphViz m = "digraph name {\n"
                    ++ (concatMap showMethod (midIRMethods m))
                    ++ "}"
  where showMethod (MidIRMethod pos name args g)
            = graphToGraphVizSubgraph g (name ++ "_")
              (name ++ " [shape=doubleoctagon,label="++show mlabel++"];\n"
              ++ name ++ " -> " ++ name ++ "_" ++ show (startVertex g) ++ ";\n")
            where mlabel = name ++ " (" ++ intercalate ", " args ++ ")"
--         toName methname v = methname ++ "_" ++ show v
--         showVertex m edges (v,bb) = toName m v ++ " [shape=box, label="
--                                     ++ (leftAlign $ show $ render (pp bb) ++ "\n") ++ "];\n"
--                                     ++ (concatMap showEdge outedges)
--             where outedges = filter (\(x,_,_) -> x == v) edges
--                   showEdge (_,b,y) = toName m v ++ " -> " ++ toName m y
--                                      ++ " [label=" ++ show b ++ "];\n"
--                   leftAlign t = subRegex (mkRegex "\\\\n") t "\\l"
