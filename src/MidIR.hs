-- | Stuff to take a hybrid AST and turn it into a MidIR

module MidIR where

import IR
import Control.Monad.State
import qualified Data.Map as Map
import Data.Array
import Data.Graphs
import Text.ParserCombinators.Parsec (SourcePos)
import Text.PrettyPrint.HughesPJ
import AST
import SymbolTable
import Data.Int
import Debug.Trace
import IR
import Data.Maybe

data MidIRField = MidIRField SourcePos String (Maybe Int64)
data MidIRMethod = MidIRMethod SourcePos String [String] ([(Int,MidBasicBlock)],[(Int,Bool,Int)], Int)

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
    = MidIRMethod (tokenPos tok) name margs ir
      where name = tokenString tok
            (margs, ir) = evalState methodToMidIR' initState
            methodToMidIR' = do (sargs', env') <- newLocalEnvEntries sargs env
                                endBlock <- newBlock [] (IRReturn methReturn)
                                startBlock <- statementToMidIR env' endBlock (-1) (-1) st
                                state <- get
                                return (sargs', (currBasicBlocks state,
                                                 currEdges state,
                                                 startBlock))
            sargs = [tokenString t | (HMethodArg _ _ t) <- args]
            irempty = LabGraph (array (0,0) []) (\i -> BasicBlock [] IRTestFalse)
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
statementToMidIR env s c b (HAssignSt _ pos loc op expr)
    = case loc of
        HPlainLocation _ pos tok ->
            let var = fromJust $ lookup (tokenString tok) env
            in expressionToMidIR env s var expr
        HArrayLocation _ pos tok expr ->
            let var = fromJust $ lookup (tokenString tok) env
            in do t <- genTmpVar
                  storeBlock <- newBlock [IndAssign pos var (OperVar t)]
                                IRTestTrue
                  addEdge storeBlock True s
                  expressionToMidIR env storeBlock t expr


expressionToMidIR :: IREnv
                  -> Int -- ^ BasicBlock on success
                  -> String -- ^ variable to output to
                  -> HExpr a -> State MidIRState Int
expressionToMidIR env s out (HBinaryOp _ pos expr1 tok expr2)
    = case tokenString tok of
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
           $+$ (text $ "start = " ++ show start)
           $+$ (nest 3 (vcat [showVertex v | v <- vertices]
                        $+$ vcat [text (show e) | e <- edges]))
        where (vertices, edges, start) = ir
              showVertex (i, bb) = text (show i)
                                   $+$ (nest 3 (pp bb))