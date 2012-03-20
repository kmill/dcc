module LowIR where

import IR
--import MidIR
import Data.Maybe
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Graphs
import AST (PP(..), SourcePos, showPos)
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ
import Data.List
import Debug.Trace

---
--- Convert to LowIR
---

data LowIRState =
    LowIRState
    { nextSymbRegId :: Int
    , regMap :: Map.Map String RegName
    , nextStringId :: Int
    , stringLabelPrefix :: String
    , stringMap :: [(String, SourcePos, String)] }

getReg :: String -> State LowIRState RegName
getReg name = do s <- get
                 case Map.lookup name (regMap s) of
                   Just r -> return r
                   Nothing ->
                     let r = SymbolicReg $ nextSymbRegId s
                     in do put $ s { nextSymbRegId = 1 + nextSymbRegId s
                                   , regMap = Map.insert name r (regMap s) }
                           return r

genReg :: State LowIRState RegName
genReg = do s <- get
            put $ s { nextSymbRegId = 1 + nextSymbRegId s }
            return $ SymbolicReg $ nextSymbRegId s
                           
-- | Main entry point to convert mid-IR to low-IR.
toLowIR :: MidIRRepr -> LowIRRepr
toLowIR (MidIRRepr fields methods)
    = LowIRRepr fields' (stringMap st) methods'
    where fields' = map toLowIRField fields
          toLowIRField (MidIRField pos name mlen)
              = LowIRField pos name (8 * (fromMaybe 1 mlen))
          globals = map (\(LowIRField _ n _) -> n ) fields'
          (methods', st) = runState (mapM (methodToLowIR globals) methods) initState
          initState = LowIRState
                      { nextSymbRegId = error "should be set later :-("
                      , regMap = error "should be set later :-("
                      , nextStringId = 0
                      , stringLabelPrefix = error "should be set later :-("
                      , stringMap = [] }

type Globals = [String]

methodToLowIR :: Globals -> MidIRMethod -> State LowIRState LowIRMethod
methodToLowIR glob (MidIRMethod pos retp name args mir)
    = do modify $ (\s -> s { nextSymbRegId=0 
                           , regMap=Map.empty
                           , stringLabelPrefix=name })
         lir <- mapGM (basicBlockToLowIR glob) mir
         makeargs <- makeArgs
         lir' <- extendWithArgs lir
         return $ LowIRMethod pos retp name
                    (length args) (fromIntegral 0) (simplifyLIR lir')
    where extendWithArgs ir
              = let st' = freshVertex ir
                in do argcode <- makeArgs    
                      let argblock = BasicBlock
                                     { blockCode=argcode
                                     , blockTest=IRTestTrue
                                     , blockTestPos=pos }
                      return $ graphWithNewStart ir st' argblock [(True, startVertex ir)]
          makeArgs = do sregs <- mapM getReg args
                        let withdests = zip3 argStackDepth argOrder sregs
                        return $ concatMap loadArg withdests
          loadArg (depth, Nothing, sreg)
              = [LoadMem pos sreg (MemAddr (X86Reg RBP) depth Nothing 0)]
          loadArg (_, Just src, sreg)
              = [RegVal pos sreg (OperReg $ X86Reg src)]

basicBlockToLowIR :: Globals -> MidBasicBlock -> State LowIRState LowBasicBlock
basicBlockToLowIR glob (BasicBlock code test testpos)
    = do (testcode, test') <- testToLowIR glob testpos test
         code' <- mapM (statementToLowIR glob) code
         return $ BasicBlock (join code' ++ testcode) test' testpos

varToLoadCode :: Globals -> SourcePos -> String
              -> State LowIRState ([LowIRInst], LowOper)
varToLoadCode glob pos s
    = case s `elem` glob of
        True -> do r <- genReg
                   return $ ( [LoadMem pos r (MemAddrPtr s)]
                            , OperReg r)
        False -> do r <- getReg s
                    return ([], OperReg r)

operToLoadCode :: Globals -> SourcePos -> MidOper
               -> State LowIRState ([LowIRInst], LowOper)
operToLoadCode g pos (OperVar s) = varToLoadCode g pos s
operToLoadCode g pos (OperConst v) = return $ ([], LowOperConst v)
operToLoadCode g pos (OperLabel s) = return $ ([], LowOperLabel s)

destToStoreCode :: Globals -> SourcePos -> String
                -> State LowIRState ([LowIRInst], RegName)
destToStoreCode glob pos name
    = case name `elem` glob of
        True -> do r <- genReg
                   return $ ( [StoreMem pos (MemAddrPtr name) (OperReg r)]
                            , r )
        False -> do r <- getReg name
                    return $ ([], r)

destToIndStoreCode :: Globals -> SourcePos -> String
                -> State LowIRState ([LowIRInst], RegName)
destToIndStoreCode glob pos name
    = case name `elem` glob of
        True -> do r <- genReg
                   let addr = MemAddrPtr name
                   return $ ( [ StoreMem pos addr (OperReg r) ]
                            , r )
        False -> do r <- getReg name
                    r' <- genReg
                    let addr = MemAddr r 0 Nothing 0
                    return $ ([ StoreMem pos addr (OperReg r') ], r')

testToLowIR :: Globals -> SourcePos -> IRTest MidOper
            -> State LowIRState ([LowIRInst], IRTest LowOper)
testToLowIR glob pos test =
    case test of
      IRTestTrue -> return ([], IRTestTrue)
      IRTestFalse -> return ([], IRTestFalse)
      IRTestBinOp op oper1 oper2 ->
          do (code1, oper1') <- operToLoadCode glob pos oper1
             (code2, oper2') <- operToLoadCode glob pos oper2
             return (code1 ++ code2, IRTestBinOp op oper1' oper2')
      IRTest oper ->
          do (code, oper') <- operToLoadCode glob pos oper
             return (code, IRTest oper')
      IRTestNot oper ->
          do (code, oper') <- operToLoadCode glob pos oper
             return (code, IRTestNot oper')
      IRReturn (Just oper) ->
          do (code, oper') <- operToLoadCode glob pos oper
             return ( code ++ [RegVal pos (X86Reg RAX) oper']
                    , IRReturn $ Just $ OperReg (X86Reg RAX))
      IRReturn Nothing -> return ([], IRReturn Nothing)
      IRTestFail s -> do (code, r) <- loadStringLit pos (fromMaybe "Error." s)
                         return (code
                                 ++ [ RegVal pos (X86Reg RDI) r
                                    , LowCallout pos "printf" 1 ],
                                 IRTestFail Nothing)

statementToLowIR :: Globals -> MidIRInst
                 -> State LowIRState [LowIRInst]
statementToLowIR glob inst =
    case inst of
      BinAssign pos dest op oper1 oper2 ->
          do (code1, reg1) <- operToLoadCode glob pos oper1
             (code2, reg2) <- operToLoadCode glob pos oper2
             (coded, regd) <- destToStoreCode glob pos dest
             return $ code1 ++ code2
                        ++ [RegBin pos regd op reg1 reg2]
                        ++ coded
      UnAssign pos dest op oper ->
          do (code1, reg1) <- operToLoadCode glob pos oper
             (coded, regd) <- destToStoreCode glob pos dest
             case op of
               OpDeref ->
                   let addr = case reg1 of
                                OperReg r -> MemAddr r 0 Nothing 0
                                LowOperConst i ->
                                    error "shouldn't addr a literal location! :-("
                                LowOperLabel s -> MemAddrPtr s
                   in return $ code1 ++ [LoadMem pos regd addr] ++ coded
               _ -> return $ code1 ++ [RegUn pos regd op reg1] ++ coded
      ValAssign pos dest oper ->
          do (code1, reg1) <- operToLoadCode glob pos oper
             (coded, regd) <- destToStoreCode glob pos dest
             return $ code1 ++ [RegVal pos regd reg1] ++ coded
      CondAssign pos dest cmp cmp1 cmp2 src ->
          do (code1, reg1) <- operToLoadCode glob pos cmp1
             (code2, reg2) <- operToLoadCode glob pos cmp2
             (codes, regs) <- operToLoadCode glob pos src
             (coded, regd) <- destToStoreCode glob pos dest
             return $ code1 ++ code2 ++ codes
                        ++ [RegCond pos regd cmp
                            reg1 reg2 regs]
                        ++ coded
      IndAssign pos dest oper ->
          do (code1, reg1) <- operToLoadCode glob pos oper
             (coded, regd) <- destToIndStoreCode glob pos dest
             return $ code1 ++ [RegVal pos regd reg1] ++ coded
      MidCall pos mret name opers ->
          do coderegs <- mapM (operToLoadCode glob pos) opers
             let coderegs' = reverse $ zip argOrder coderegs
             (coded, regd) <- case mret of
                                Just rret -> destToStoreCode glob pos rret
                                Nothing -> error "MidCall lowir :-("
             return $ (concatMap handleArg coderegs')
                        ++ [ LowCall pos name (length opers) ]
                        ++ (case mret of
                               Just rret -> [ RegBin pos (X86Reg RSP) OpAdd 
                                                         (LowOperConst $ fromIntegral $ 8 * (max 0 $ (length opers) - 6) ) 
                                                         (OperReg (X86Reg RSP) )
                                            , RegVal pos regd (OperReg (X86Reg RAX))]
                                            ++ coded
                               Nothing -> [])
          where handleArg (Nothing, (code, sreg))
                    = code ++ [RegPush pos sreg]
                handleArg ((Just dreg), (code, src))
                    = code ++ [RegVal pos (X86Reg dreg) src]
      MidCallout pos mret name opers ->
          do coderegs <- mapM (either (loadStringLit pos) (operToLoadCode glob pos))
                         opers
             let coderegs' = reverse $ zip argOrder coderegs
             (coded, regd) <- case mret of
                                Just rret -> destToStoreCode glob pos rret
                                Nothing -> error "MidCall lowir :-("
             return $ (concatMap handleArg coderegs')
                         ++ [ LowCallout pos name (length opers) ]
                         ++ (case mret of
                               Just rret -> [ RegBin pos (X86Reg RSP) OpAdd 
                                                         (LowOperConst $ fromIntegral $ 8 * (max 0 $ (length opers) - 6) ) 
                                                         (OperReg (X86Reg RSP) )
                                            , RegVal pos regd (OperReg (X86Reg RAX))]
                                            ++ coded
                               Nothing -> [])
          where handleArg (Nothing, (code, sreg))
                    = code ++ [RegPush pos sreg]
                handleArg ((Just dreg), (code, src))
                    = code ++ [RegVal pos (X86Reg dreg) src]

loadStringLit :: SourcePos -> String
              -> State LowIRState ([LowIRInst], LowOper)
loadStringLit pos str
    = do s <- get
         let sname = "string_"
                     ++ (stringLabelPrefix s)
                     ++ "_" ++ (show $ nextStringId s)
         put $ s { nextStringId = nextStringId s + 1
                 , stringMap = (sname, pos, str):(stringMap s) }
         r <- genReg
         return $ ( [RegVal pos r (LowOperLabel sname)]
                  , OperReg r )


---
--- Simplify LIR
---

simplifyLIR :: LowIRGraph -> LowIRGraph
simplifyLIR lir = normalizeBlocks $ mergeRegs $ normalizeBlocks lir

mergeRegs :: LowIRGraph -> LowIRGraph
mergeRegs lir
    = let keepRegs = Map.map (\(keep,_,_) -> keep) (determineExtents lir)
      in mapGWithKey (\k bb -> fixBB (fromJust $ Map.lookup k keepRegs) bb) lir
    where fixBB alive bb
              = let alive' = (X86Reg RSP):(X86Reg RBP):alive
                    (trees, test) = evalLowInstrs alive' Map.empty []
                                    (blockCode bb) (blockTest bb)
                in evalLowIRForest alive' (blockTestPos bb) trees test
--            error $ show alive ++ "\n" ++ show bb
          

getFreshSReg :: [RegName] -> RegName
getFreshSReg regs = head $ filter (`notElem` regs) (map SymbolicReg [0..])

data LowIRTree = LowOperNode LowOper
               | RegStoreNode SourcePos RegName LowIRTree
               | RegBinOpNode SourcePos BinOp LowIRTree LowIRTree
               | RegUnOpNode SourcePos UnOp LowIRTree
               | RegCondNode SourcePos CmpBinOp LowIRTree LowIRTree LowIRTree
               | RegPushNode SourcePos LowIRTree
               | StoreMemNode SourcePos LowIRTree LowIRTree
               | LoadMemNode SourcePos LowIRTree
               | LowCallNode SourcePos String Int
               | LowCalloutNode SourcePos String Int

getReplaceables :: LowIRTree -> [LowIRTree]
getReplaceables (LowOperNode _) = []
getReplaceables (RegStoreNode _ _ t) = [t]
getReplaceables (RegBinOpNode _ _ t1 t2) = [t1,t2]
getReplaceables (RegUnOpNode _ _ t) = [t]
getReplaceables (RegCondNode _ _ t1 t2 t3) = [t1,t2,t3]
getReplaceables (RegPushNode _ t) = [t]
getReplaceables (StoreMemNode _ t1 t2) = [t1,t2]
getReplaceables (LoadMemNode _ t) = [t]
getReplaceables (LowCallNode _ _ _) = []
getReplaceables (LowCalloutNode _ _ _) = []

setReplaceables :: LowIRTree -> [LowIRTree] -> LowIRTree
setReplaceables n@(LowOperNode _) [] = n
setReplaceables (RegStoreNode pos name _) [t] = RegStoreNode pos name t
setReplaceables (RegBinOpNode pos op _ _) [t1,t2] = RegBinOpNode pos op t1 t2
setReplaceables (RegUnOpNode pos op _) [t] = RegUnOpNode pos op t
setReplaceables (RegCondNode pos op _ _ _) [t1,t2,t3] = RegCondNode pos op t1 t2 t3
setReplaceables (RegPushNode pos _) [t] = RegPushNode pos t
setReplaceables (StoreMemNode pos _ _) [t1,t2] = StoreMemNode pos t1 t2
setReplaceables (LoadMemNode pos _) [t] = LoadMemNode pos t
setReplaceables n@(LowCallNode _ _ _) [] = n
setReplaceables n@(LowCalloutNode _ _ _) [] = n
setReplaceables _ _ = error "setReplaceables :-("

instance Show LowIRTree where
  show t = render $ pp t

instance PP LowIRTree where
  pp (RegStoreNode _ r oper) = text (show r ++ " :=") 
                               $+$ (nest 3 $ pp oper)
  pp (RegBinOpNode _ op oper1 oper2)
      = text (show op)
         $+$ (nest 3 $ pp oper1)
         $+$ (nest 3 $ pp oper2)
  pp (RegUnOpNode _ op oper1)
      = text (show op)
         $+$ (nest 3 $ pp oper1)
  pp (RegCondNode _ cmp cmp1 cmp2 oper)
      = text "cmove"
         $+$ (nest 3 $ text $ show cmp)
         $+$ (nest 6 $ pp cmp1)
         $+$ (nest 6 $ pp cmp2)
         $+$ (nest 3 $ pp oper)
  pp (RegPushNode _ oper)
      = text "push"
        $+$ (nest 3 $ pp oper)
  pp (StoreMemNode _ addr oper)
      = text "memstore"
         $+$ (nest 3 $ pp addr)
         $+$ (nest 3 $ pp oper)
  pp (LoadMemNode _ addr)
      = text "memload"
        $+$ (nest 3 $ pp addr)
  pp (LowCallNode _ name nargs)
      = text ("call " ++ show name ++ " " ++ show nargs)
  pp (LowCalloutNode _ name nargs)
        = text ("callout " ++ show name ++ " " ++ show nargs)
  pp (LowOperNode o) = text $ show o

timesUsed :: Int -> RegName -> [LowIRInst] -> IRTest LowOper -> Int
timesUsed cnt r [] test = cnt + (length $ filter (==r) (checkTestExtents test))
timesUsed cnt r (inst:insts) test
    = let (d, a) = checkExtents inst
          cnt' = cnt + (length $ filter (==r) a)
      in if r `elem` d
         then cnt'
         else timesUsed cnt' r insts test

regLookup :: LowOper -> Map.Map RegName LowIRTree -> LowIRTree
regLookup (OperReg r) regmap
    = case Map.lookup r regmap of
        Nothing -> LowOperNode (OperReg r)
        Just x -> x
regLookup x regmap = LowOperNode x

evalLowInstrs :: [RegName] -> Map.Map RegName LowIRTree
              -> [LowIRTree] -> [LowIRInst] -> IRTest LowOper
              -> ([LowIRTree], IRTest LowIRTree)
evalLowInstrs alive regMap evaled [] test
    = case test of
        IRTestTrue -> (evaled, IRTestTrue)
        IRTestFalse -> (evaled, IRTestFalse)
        IRTestBinOp op oper1 oper2 ->
            (evaled, IRTestBinOp op (regLookup oper1 regMap) (regLookup oper2 regMap))
        IRTest oper ->
            (evaled, IRTest (regLookup oper regMap))
        IRTestNot oper ->
            (evaled, IRTestNot (regLookup oper regMap))
        IRReturn Nothing ->
            (evaled, IRReturn Nothing)
        IRReturn (Just oper) ->
            (evaled, IRReturn $ Just (regLookup oper regMap))
        IRTestFail x ->
            (evaled, IRTestFail x)
evalLowInstrs alive regMap evaled (instr:instrs) test
    = case instr of
        RegBin pos rd op oper1 oper2 ->
            continueWithStore pos rd False $
            RegBinOpNode pos op (regLookup oper1 regMap) (regLookup oper2 regMap)
        RegUn pos rd op oper ->
            continueWithStore pos rd False $
            RegUnOpNode pos op (regLookup oper regMap)
        RegVal pos rd oper ->
            continueWithStore pos rd False (regLookup oper regMap)
        RegCond pos rd cmp cmp1 cmp2 oper ->
            continueWithStore pos rd True $
            RegCondNode pos cmp
                 (regLookup cmp1 regMap) (regLookup cmp2 regMap)
                 (regLookup oper regMap)
        RegPush pos oper ->
            continue $ RegPushNode pos (regLookup oper regMap)
        StoreMem pos mem oper ->
            continue $ StoreMemNode pos (evalMem pos mem) (regLookup oper regMap)
        LoadMem pos rd mem ->
            continueWithStore pos rd False $ LoadMemNode pos (evalMem pos mem)
        LowCall pos name nargs ->
            continueWithStoreForceRegs pos (X86Reg RAX)
                 (reverse [X86Reg r | r <- catMaybes (take nargs argOrder)]) $
            LowCallNode pos name nargs
        LowCallout pos name nargs ->
            continueWithStoreForceRegs pos (X86Reg RAX)
                 (reverse [X86Reg r | r <- catMaybes (take nargs argOrder)]) $
            LowCalloutNode pos name nargs
      where
        -- 'dobefore' represents whether a previous version of rd
        -- should be stored before the current instruction. for
        -- conditional move.
        continueWithStore pos rd dobefore tree
            = let times = timesUsed 0 rd instrs test
              in case times of
                   0 -> if rd `elem` alive
                        then continueWithStoreForce pos rd dobefore tree
                        else -- optimize out!
                            evalLowInstrs alive regMap evaled instrs test
                   1 -> if rd `elem` alive
                        then continueWithStoreForce pos rd dobefore tree
                        else evalLowInstrs alive (Map.insert rd tree regMap)
                             evaled instrs test
                   _ -> continueWithStoreForce pos rd dobefore tree
        continueWithStoreForce pos rd dobefore tree
            = evalLowInstrs alive (Map.delete rd regMap)
              (evaled++before++[RegStoreNode pos rd tree])
              instrs test
            where before = if dobefore
                           then case Map.lookup rd regMap of
                                  Just t -> [RegStoreNode pos rd t]
                                  Nothing -> []
                           else []
        continueWithStoreForceRegs pos rd regsbefore tree
            = evalLowInstrs alive (Map.delete rd regMap)
              (evaled++before++[RegStoreNode pos rd tree])
              instrs test
            where storebefore r = case Map.lookup r regMap of
                                  Just t -> [RegStoreNode pos r t]
                                  Nothing -> []
                  before = concatMap storebefore regsbefore
        continue tree = evalLowInstrs alive regMap
                        (evaled ++ [tree])
                        instrs test
        -- let's turn the mem addresses into trees, too!
        evalMem pos (MemAddrPtr s) = LowOperNode $ LowOperLabel s
        evalMem pos (MemAddr br 0 Nothing _)
            = (regLookup (OperReg br) regMap)
        evalMem pos (MemAddr br d Nothing _)
            = RegBinOpNode pos OpAdd (regLookup (OperReg br) regMap)
              (LowOperNode $ LowOperConst $ fromIntegral d)
        evalMem pos (MemAddr br d (Just or) s)
            = RegBinOpNode pos OpAdd (regLookup (OperReg br) regMap) $
              RegBinOpNode pos OpAdd (LowOperNode $ LowOperConst $ fromIntegral d) $
              RegBinOpNode pos OpMul (LowOperNode $ LowOperConst $ fromIntegral s) $
                 (regLookup (OperReg or) regMap)

evalLowIRForest :: [RegName] -> SourcePos -> [LowIRTree] -> IRTest LowIRTree
                -> LowBasicBlock
evalLowIRForest used pos nodes test
    = let code = concatMap (evalLowIRTree used) nodes
          (testcode, test') = evalLowIRTreeTest used pos test
      in BasicBlock (code ++ testcode) test' pos

evalLowIRTree :: [RegName] -> LowIRTree -> [LowIRInst]
evalLowIRTree used node = runRuleset used node lowIRTreeToLowIR_rules

evalLowIRTreeTest :: [RegName] -> SourcePos -> IRTest LowIRTree
              -> ([LowIRInst], IRTest LowOper)
evalLowIRTreeTest used pos test
    = case test of
        IRTestTrue -> ([], IRTestTrue)
        IRTestFalse -> ([], IRTestFalse)
        IRTestBinOp op oper1 oper2 ->
            let reg1 = getFreshSReg used
                used' = reg1:used
                reg2 = getFreshSReg used'
                used'' = reg2:used'
                code1 = evalLowIRTree used'' (RegStoreNode pos reg1 oper1)
                code2 = evalLowIRTree used'' (RegStoreNode pos reg2 oper2)
            in (code1 ++ code2, IRTestBinOp op (OperReg reg1) (OperReg reg2))
        IRTest (RegBinOpNode pos (OpBinCmp op) oper1 oper2) ->
            evalLowIRTreeTest used pos (IRTestBinOp op oper1 oper2)
        IRTest oper ->
            let reg1 = getFreshSReg used
                used' = reg1:used
                code1 = evalLowIRTree used' (RegStoreNode pos reg1 oper)
            in (code1, IRTest (OperReg reg1))
        IRTestNot (RegBinOpNode pos (OpBinCmp op) oper1 oper2) ->
            evalLowIRTreeTest used pos (IRTestBinOp (negateCmpBinOp op) oper1 oper2)
        IRTest oper ->
            let reg1 = getFreshSReg used
                used' = reg1:used
                code1 = evalLowIRTree used' (RegStoreNode pos reg1 oper)
            in (code1, IRTestNot (OperReg reg1))
        IRReturn Nothing -> ([], IRReturn Nothing)
        IRReturn (Just a) ->
            let code = evalLowIRTree used (RegStoreNode pos (X86Reg RAX) a)
            in (code, IRReturn (Just $ OperReg $ X86Reg RAX))
        IRTestFail ms -> ([], IRTestFail ms)

data IRTreeRuleMonad a = IRTreeRuleMonad
    { runIRTreeRuleMonad :: LowIRTree -> [RegName] -> [([RegName], a)] }

instance Monad IRTreeRuleMonad where
    return a = IRTreeRuleMonad $ \ tree used -> [(used, a)]
    (IRTreeRuleMonad a) >>= f
        = IRTreeRuleMonad $ \ tree used ->
          concatMap (\ (used', av) -> runIRTreeRuleMonad (f av) tree used' ) (a tree used)
    fail _ = mzero

instance MonadPlus IRTreeRuleMonad where
    mzero = IRTreeRuleMonad $ \ tree used -> []
    (IRTreeRuleMonad a) `mplus` (IRTreeRuleMonad b)
        = IRTreeRuleMonad $ \ tree used -> (a tree used) ++ (b tree used)

getNode :: IRTreeRuleMonad LowIRTree
getNode = IRTreeRuleMonad $ \ tree used -> [(used, tree)]

getFreeRegister :: IRTreeRuleMonad RegName
getFreeRegister = IRTreeRuleMonad $ \ tree used ->
                  let reg = getFreshSReg used
                  in [(reg:used, reg)]

type IRTreeEmit = (Maybe LowIRTree, [LowIRInst])

emitAndFinish :: [LowIRInst] -> IRTreeRuleMonad IRTreeEmit
emitAndFinish insts = return (Nothing, insts)

replaceWith :: LowIRTree -> IRTreeRuleMonad IRTreeEmit
replaceWith tree = return (Just tree, [])

replaceAndEmit :: LowIRTree -> [LowIRInst] -> IRTreeRuleMonad IRTreeEmit
replaceAndEmit tree insts = return (Just tree, insts)

withTree :: LowIRTree -> IRTreeRuleMonad a -> IRTreeRuleMonad a
withTree tree (IRTreeRuleMonad m)
    = IRTreeRuleMonad $ \ _ used -> m tree used

runManyRules :: [IRTreeRuleMonad a] -> IRTreeRuleMonad a
runManyRules rules = IRTreeRuleMonad $ \ tree used ->
                     concatMap (\r -> runIRTreeRuleMonad r tree used) rules

runRuleSubtrees :: IRTreeRuleMonad IRTreeEmit -> IRTreeRuleMonad IRTreeEmit 
runRuleSubtrees rule = rule `mplus` do node <- getNode
                                       let subs = getReplaceables node
                                       emits <- flip mapM subs
                                                (\sub ->
                                                 withTree sub subtreerule)
                                       (subs', code) <- combineEmits emits
                                       let node' = setReplaceables node subs'
                                       withTree node' rule
    where
      combineEmits :: [IRTreeEmit] -> IRTreeRuleMonad ([LowIRTree], [LowIRInst])
      combineEmits emits = do unmaybed <- mapM unmaybe emits
                              let (subs', codes) = unzip unmaybed
                              return (subs', concat codes)
      unmaybe :: IRTreeEmit -> IRTreeRuleMonad (LowIRTree, [LowIRInst])
      unmaybe emit = do let (Just t, code) = emit
                        return (t, code)
      noop :: IRTreeRuleMonad IRTreeEmit
      noop = do node <- getNode
                (trace (show node) replaceWith) node
      subtreerule = (runRuleSubtrees rule) `mplus` noop

runRuleset :: [RegName] -> LowIRTree -> IRTreeRuleMonad IRTreeEmit -> [LowIRInst]
runRuleset used tree rule = case possibilities of
                              [] -> error ("No rewrite rule for\n" ++ show tree)
                              poss -> minimumBy compareBy poss
  where rootRule = do (Nothing, code) <- runRuleSubtrees rule
                      return code
        possibilities = map snd $ runIRTreeRuleMonad rootRule tree used
        optimizeFor = sum . (map costs)
        costs :: LowIRInst -> Int
        costs (RegBin _ _ _ _ _) = 3
        costs (RegUn _ _ _ _) = 2
        costs (RegVal _ _ _) = 2
        costs (RegCond _ _ _ _ _ _) = 4
        costs (RegPush _ _) = 1
        costs (StoreMem _ _ _) = 2
        costs (LoadMem _ _ _) = 2
        costs (LowCall _ _ _) = 1
        costs (LowCallout _ _ _) = 1
        compareBy a b = compare (optimizeFor a) (optimizeFor b)

lowIRTreeToLowIR_rules = foldr1 mplus rules
    where rules =
              [ ---
                --- Stores
                ---
                do -- basic store
                  (RegStoreNode pos dest (LowOperNode oper)) <- getNode
                  emitAndFinish [RegVal pos dest oper]
              , do -- store from binop
                  (RegStoreNode _ dest (RegBinOpNode pos op
                                        (LowOperNode oper1)
                                        (LowOperNode oper2))) <- getNode
                  emitAndFinish [RegBin pos dest op oper1 oper2]
              , do -- store from unop
                  (RegStoreNode _ dest (RegUnOpNode pos op
                                        (LowOperNode oper))) <- getNode
                  emitAndFinish [RegUn pos dest op oper]
              , do -- store from cond
                  (RegStoreNode _ dest (RegCondNode pos cmp
                                        (LowOperNode cmp1)
                                        (LowOperNode cmp2)
                                        (LowOperNode src))) <- getNode
                  emitAndFinish [RegCond pos dest cmp cmp1 cmp2 src]
              , do -- store from load mem; src is (reg)
                  (RegStoreNode _ dest
                                (LoadMemNode pos (LowOperNode (OperReg reg))))
                      <- getNode
                  let mem = MemAddr reg 0 Nothing 0
                  emitAndFinish [LoadMem pos dest mem]
              , do -- store from load mem; src is (disp+reg)
                   (RegStoreNode _ dest
                                 (LoadMemNode pos
                                  (RegBinOpNode _ OpAdd
                                   (LowOperNode (LowOperConst disp))
                                   (LowOperNode (OperReg reg)))))
                       <- getNode
                   -- guard $ disp ... make sure and check displacement size!
                   let mem = MemAddr reg (fromIntegral disp) Nothing 0
                   emitAndFinish [LoadMem pos dest mem]
              , do -- store from load mem; src is (label)
                  (RegStoreNode _ dest
                                (LoadMemNode pos (LowOperNode (LowOperLabel label))))
                      <- getNode
                  let mem = MemAddrPtr label
                  emitAndFinish [LoadMem pos dest mem]
              , do -- store from call
                   (RegStoreNode _ (X86Reg RAX)
                                     (LowCallNode pos name numargs))
                       <- getNode
                   emitAndFinish [LowCall pos name numargs]
              , do -- store from callout
                   (RegStoreNode _ (X86Reg RAX)
                                     (LowCalloutNode pos name numargs))
                       <- getNode
                   emitAndFinish [LowCallout pos name numargs]
              ---
              --- Push
              ---
              , do -- basic push
                   (RegPushNode pos (LowOperNode oper)) <- getNode
                   emitAndFinish [RegPush pos oper]
              ---
              --- Store mem node
              ---
              , do -- basic store to mem; dest is (reg)
                   (StoreMemNode pos (LowOperNode (OperReg dest)) (LowOperNode src))
                       <- getNode
                   let mem = MemAddr dest 0 Nothing 0
                   emitAndFinish [StoreMem pos mem src]
              , do -- basic store to mem; dest is (disp+reg)
                   (StoreMemNode pos
                    (RegBinOpNode _ OpAdd
                     (LowOperNode (LowOperConst disp))
                     (LowOperNode (OperReg reg)))
                    (LowOperNode src)) <- getNode
                   -- check displacement size? TODO
                   let mem = MemAddr reg (fromIntegral disp) Nothing 0
                   emitAndFinish [StoreMem pos mem src]
              , do -- store to a label
                  (StoreMemNode pos
                   (LowOperNode (LowOperLabel label)) 
                   (LowOperNode src)) <- getNode
                  let mem = MemAddrPtr label
                  emitAndFinish [StoreMem pos mem src]
              ---
              --- Binary operators
              ---
              , do -- binary op with two constants
                   (RegBinOpNode pos op
                    (LowOperNode (LowOperConst oper1))
                    (LowOperNode (LowOperConst oper2))) <- getNode
                   guard $ op /= OpDiv && oper2 /= 0
                   let res = case op of
                               OpAdd -> oper1 + oper2
                               OpSub -> oper1 - oper2
                               OpMul -> oper1 * oper2
                               OpDiv -> oper1 `div` oper2
                               OpMod -> oper1 `rem` oper2
                               OpBinCmp CmpLT -> boolToInt (oper1 < oper2)
                               OpBinCmp CmpLTE -> boolToInt (oper1 <= oper2)
                               OpBinCmp CmpGT -> boolToInt (oper1 > oper2)
                               OpBinCmp CmpGTE -> boolToInt (oper1 >= oper2)
                               OpBinCmp CmpEQ -> boolToInt (oper1 == oper2)
                               OpBinCmp CmpNEQ -> boolToInt (oper1 /= oper2)
                   replaceWith (LowOperNode (LowOperConst res))
              , do -- normal binary op
                   (RegBinOpNode pos op
                    (LowOperNode oper1) (LowOperNode oper2)) <- getNode
                   reg <- getFreeRegister
                   replaceAndEmit (LowOperNode (OperReg reg)) $
                                      [ RegBin pos reg op oper1 oper2 ]
              ---
              --- Unary operators
              ---
              , do -- Unary op with a constant
                   (RegUnOpNode pos op (LowOperNode (LowOperConst oper)))
                       <- getNode
                   let res = case op of
                               OpNot -> boolToInt (oper /= 0)
                               OpNeg -> negate res
                   replaceWith (LowOperNode (LowOperConst res))
              , do -- basic unary op
                   (RegUnOpNode pos op (LowOperNode oper)) <- getNode
                   reg <- getFreeRegister
                   replaceAndEmit (LowOperNode (OperReg reg)) $
                                      [ RegUn pos reg op oper ]
              ---
              --- "nullary" operators
              ---
              , do -- load label into reg (not ptr dest, but ptr)
                   (LowOperNode (LowOperLabel label)) <- getNode
                   reg <- getFreeRegister
                   replaceAndEmit (LowOperNode (OperReg reg)) $
                                      [ RegVal noPosition reg (LowOperLabel label) ]
--               , do -- a register's a register!
--                    (LowOperNode (OperReg reg)) <- getNode
--                    replaceWith (LowOperNode (OperReg reg))
--               , do -- a constant's a constant!
--                    (LowOperNode (LowOperConst c)) <- getNode
--                    replaceWith (LowOperNode (LowOperConst c))
              ---
              --- Load mem
              ---
              , do -- load mem; dest is (reg)
                  (LoadMemNode pos (LowOperNode (OperReg reg)))
                      <- getNode
                  let mem = MemAddr reg 0 Nothing 0
                  dest <- getFreeRegister
                  replaceAndEmit (LowOperNode (OperReg dest))
                                     [LoadMem pos reg mem]
              , do -- load mem; dest is (disp+reg)
                   (LoadMemNode pos
                    (RegBinOpNode _ OpAdd
                     (LowOperNode (LowOperConst disp))
                     (LowOperNode (OperReg reg))))
                       <- getNode
                   -- guard $ disp ... make sure and check displacement size!
                   let mem = MemAddr reg (fromIntegral disp) Nothing 0
                   dest <- getFreeRegister
                   replaceAndEmit (LowOperNode (OperReg dest)) 
                                      [LoadMem pos dest mem]
              , do -- load mem from label
                   (LoadMemNode pos (LowOperNode (LowOperLabel label))) <- getNode
                   dest <- getFreeRegister
                   let mem = MemAddrPtr label
                   replaceAndEmit (LowOperNode (OperReg dest))
                                      [LoadMem pos dest mem]
              -- load mem from const shouldn't happen
              ]

---
--- Show LowIRRepr!
---

instance Show LowIRRepr where
    show = render . pp

instance PP LowIRRepr where
    pp m = text "LowIR"
           $+$ (nest 3 ((text "fields" $+$ (nest 3 fields))
                        $+$ (text "strings" $+$ (nest 3 strings))
                        $+$ (text "methods" $+$ (nest 3 methods))))
      where fields = vcat (map showField $ lowIRFields m)
            showField (LowIRField pos s size)
              = text s
                <+> text ("[" ++ show size ++ " bytes]")
                <+> text ("{" ++ show pos ++ "}")
            strings = vcat (map showString $ lowIRStrings m)
            showString (name, pos, s)
                = text name
                  <+> text (show s)
                  <+> text ("{" ++ show pos ++ "}")
            methods = vcat [pp m | m <- lowIRMethods m]

instance PP LowIRMethod where
    pp (LowIRMethod pos retp name nargs locspace ir)
        = text ("{" ++ show pos ++ "}")
           $+$ (if retp then text "ret" else text "void") <+> text name
           <+> text (show nargs) <+> brackets (text (show locspace))
           $+$ (text $ "start = " ++ show (startVertex ir))
           $+$ (nest 3 (vcat [showVertex v | v <- labels ir]))
        where showVertex (i,bb) = text (show i)
                                   <+> (nest 3 (pp bb))
                                   $+$ (nest 5 (vcat (map showEdge outedges)))
                                  $+$ (nest 3 (text $ show $ Map.lookup i rmap))
                  where outedges = adjEdges ir i
                        showEdge (b,y) = text (show b ++ " -> " ++ show y)
              rmap = determineExtents ir
                        

lowIRtoGraphViz m = "digraph name {\n"
                    ++ (showFields (lowIRFields m))
                    -- ++ (showStrings (lowIRStrings m))
                    ++ (concatMap showMethod (lowIRMethods m))
                    ++ "}"
  where showMethod (LowIRMethod pos retp name nargs locspace g)
            = graphToGraphVizSubgraph g (name ++ "_")
              (name ++ " [shape=doubleoctagon,label="++show mlabel++"];\n"
              ++ name ++ " -> " ++ name ++ "_" ++ show (startVertex g) ++ ";\n")
            where mlabel = (if retp then "ret " else "void ")
                           ++ name ++ " " ++ show nargs
                           ++ " [" ++ show locspace ++ "]"
        showField (LowIRField pos name size)
            = "{" ++ name ++ "|" ++ show size ++ " bytes}"
        showFields fields = "_fields_ [shape=record,label=\"fields|{"
                            ++ intercalate "|" (map showField fields)
                            ++ "}\"];\n"
        showStrings strings = "_strings_ [shape=record,label="
                              ++ show ("strings|{"
                                       ++ intercalate "|" (map showString strings)
                                       ++ "}")
                              ++ "];\n"
        showString (name, pos, str)
            = "{" ++ name ++ "|" ++ showPos pos ++ "|" ++ show str ++ "}"