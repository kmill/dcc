{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

module CodeGenerate where

import Compiler.Hoopl
import Compiler.Hoopl.Fuel
import qualified Assembly as A
import Assembly(checkIf32Bit, rmToIRM, LowIRRepr(..), LowIRField(..))
import qualified IR as I
import IR(MidIRExpr, VarName, Showing)
import AST(noPosition, SourcePos, showPos)
import Control.Monad
import Data.Maybe
import Data.List
import Data.Int
import qualified Data.Set as S
import Dataflow
import Debug.Trace

type GM = I.GM

toAss :: I.MidIRRepr -> GM LowIRRepr
toAss (I.MidIRRepr fields strs meths graph)
    = do graph' <- mgraph'
         return $ LowIRRepr (map toLowField fields) strs meths graph'
    where GMany _ body _ = graph
          mgraph' = do graphs' <- mapM f (mapElems body)
                       return $ foldl (|*><*|) emptyClosedGraph graphs'
          f :: Block I.MidIRInst C C -> GM (Graph A.Asm C C)
          f block = do e' <- toAsm e
                       inner' <- mapM toAsm inner
                       x' <- toAsm x
                       return $ e' <*> catGraphs inner' <*> x'
              where (me, inner, mx) = blockToNodeList block
                    e :: I.MidIRInst C O
                    x :: I.MidIRInst O C
                    e = case me of
                          JustC e' -> e'
                    x = case mx of
                          JustC x' -> x'
          toLowField (I.MidIRField pos name Nothing)
              = LowIRField pos name 8
          toLowField (I.MidIRField pos name (Just len))
              = LowIRField pos name (8 * len)

          mlabels = map I.methodEntry meths

          toAsm :: forall e x. I.MidIRInst e x -> GM (Graph A.Asm e x)
          toAsm e = do as <- rCGM $ instToAsm e
                       case as of
                         [] -> error $ "No output for " ++ show e
                         a:_ -> return a


-- | CGM is "Code Gen Monad"
data CGM a = CGM { rCGM :: GM [a] }

instance Monad CGM where
    return x = CGM $ return [x]
    ma >>= f = CGM $ do as <- rCGM ma
                        as' <- sequence (map (rCGM . f) as)
                        return $ concat as'
    fail _ = mzero

instance Functor CGM where
    fmap f ma = do a <- ma
                   return $ f a

instance MonadPlus CGM where
    mzero = CGM $ return []
    mplus (CGM mas) (CGM mbs)
        = CGM $ do as <- mas
                   bs <- mbs
                   return $ as ++ bs

-- | cuts the computation down to one branch
mcut :: CGM a -> CGM a
mcut (CGM mas) = CGM $ do as <- mas
                          case as of
                            [] -> return []
                            a:_ -> return [a]

-- | just take the first!
runCGM :: CGM a -> GM a
runCGM (CGM mxs) = do xs <- mxs
                      return $ head xs

genTmpReg :: CGM A.Reg
genTmpReg = CGM $ do s <- I.genUniqueName "s"
                     return [A.SReg s]

--genSpill :: Reg -> CGM (Graph A.Asm O O)
--genReload :: String -> CGM
--giveBackTmpReg :: CGM A.Reg

instToAsm :: forall e x. I.MidIRInst e x -> CGM (Graph A.Asm e x)
instToAsm (I.Label pos l) = return $ mkFirst $ A.Label pos l
instToAsm (I.PostEnter pos l) = return $ mkFirst $ A.Label pos l
instToAsm (I.Enter pos l args)
    = do return $ mkFirst (A.Enter pos l 0)
                    <*> (genPushRegs pos A.calleeSaved)
                    <*> (genLoadArgs pos args)
instToAsm (I.Store pos d sexp)
    = do (gd, s) <- expToIRM sexp
         return $ gd <*> mkMiddle (A.MovIRMtoR pos s (A.SReg $ show d))
instToAsm (I.IndStore pos dexp sexp)
    = do (gd, d) <- expToMem dexp
         (gs, s) <- expToIR sexp
         return $ gd <*> gs
                    <*> mkMiddle (A.MovIRtoM pos s d)
instToAsm (I.Call pos d name args)
    = do (gs, vars) <- unzip `fmap` mapM expToIRM args
         return $ catGraphs gs
                    <*> genPushRegs pos A.callerSaved
                    <*> genSetArgs pos vars
                    <*> mkMiddle (A.Call pos (length args) (A.Imm32Label name 0))
                    <*> genResetSP pos args
                    <*> genPopRegs pos A.callerSaved
                    <*> mkMiddle (A.mov pos (A.MReg A.RAX) (A.SReg $ show d))
instToAsm (I.Callout pos d name args)
    = do (gs, vars) <- unzip `fmap` mapM expToIRM args
         return $ catGraphs gs
                    <*> genPushRegs pos A.callerSaved
                    <*> genSetArgs pos vars
                    <*> mkMiddle (A.mov pos (A.Imm32 0) (A.MReg A.RAX))
                    <*> mkMiddle (A.Callout pos (length args) (A.Imm32Label name 0))
                    <*> genResetSP pos args
                    <*> genPopRegs pos A.callerSaved
                    <*> mkMiddle (A.mov pos (A.MReg A.RAX) (A.SReg $ show d))
instToAsm (I.Branch pos l)
    = return $ mkLast $ A.Jmp pos (A.Imm32BlockLabel l 0)
instToAsm (I.CondBranch pos cexp tl fl)
    = do (g, flag) <- expToFlag cexp
         return $ g <*> (mkLast $ A.JCond pos flag (A.Imm32BlockLabel tl 0) fl)
instToAsm (I.Return pos Nothing)
    = return $ genPopRegs pos A.calleeSaved
               <*> (mkMiddle $ A.Leave pos)
               <*> (mkLast $ A.Ret pos False)
instToAsm (I.Return pos (Just exp))
    = do (g, irm) <- expToIRM exp
         return $ g <*> mkMiddle (A.MovIRMtoR pos irm (A.MReg A.RAX))
                    <*> genPopRegs pos A.calleeSaved
                    <*> (mkMiddle $ A.Leave pos)
                    <*> mkLast (A.Ret pos True)
instToAsm (I.Fail pos)
    = return $ mkMiddles [ A.mov pos (A.Imm32 1) (A.MReg A.RDI)
                         , A.mov pos (A.Imm32 1) (A.MReg A.RAX)
                         , A.Call pos 1 (A.Imm32Label "exit" 0) ]
               <*> mkLast (A.ExitFail pos)

genSetArgs :: SourcePos -> [A.OperIRM] -> Graph A.Asm O O
genSetArgs pos args = catGraphs $ map genset $ reverse (zip args A.argOrder)
    where genset (a, Nothing) = mkMiddle $ A.Push pos a
          genset (a, Just d) = mkMiddle $ A.MovIRMtoR pos a (A.MReg d)
genResetSP :: SourcePos -> [MidIRExpr] -> Graph A.Asm O O
genResetSP pos args = if length args - 6 > 0
                      then mkMiddle $
                           A.ALU_IRMtoR pos A.Add
                                (A.IRM_I $ A.Imm32 $
                                  fromIntegral $ 8 * (length args - 6))
                                (A.MReg A.RSP)
                      else GNil

genLoadArgs :: SourcePos -> [VarName] -> Graph A.Asm O O
genLoadArgs pos args = catGraphs $ map genload $ zip args A.argLocation
    where genload (a, Right reg)
              = mkMiddle $ A.MovIRMtoR pos (A.IRM_R reg) (A.SReg $ show a)
          genload (a, Left mem)
              = mkMiddle $ A.MovIRMtoR pos (A.IRM_M mem) (A.SReg $ show a)

genPushRegs :: SourcePos -> [A.X86Reg] -> Graph A.Asm O O
genPushRegs pos regs = catGraphs $ map genpush regs
    where genpush reg = mkMiddle $ A.Push pos $ A.IRM_R (A.MReg reg)
genPopRegs :: SourcePos -> [A.X86Reg] -> Graph A.Asm O O
genPopRegs pos regs = catGraphs $ map genpop $ reverse regs
    where genpop reg = mkMiddle $ A.Pop pos $ A.RM_R (A.MReg reg)

expTo' :: (a -> b) -> CGM (Graph A.Asm O O, a) -> CGM (Graph A.Asm O O, b)
expTo' f m = do (g, a) <- m
                return $ (g, f a)
expITo' :: (a -> b) -> CGM a -> CGM (Graph A.Asm O O, b)
expITo' f m = do a <- m
                 return $ (GNil, f a)

expToIRM :: MidIRExpr -> CGM (Graph A.Asm O O, A.OperIRM)
expToIRM e = expITo' A.IRM_I (expToI e)
             `mplus` expTo' A.IRM_M (expToM e)
             `mplus` expTo' A.IRM_R (expToR e)
expToIR :: MidIRExpr -> CGM (Graph A.Asm O O, A.OperIR)
expToIR e = expITo' A.IR_I (expToI e)
            `mplus` expTo' A.IR_R (expToR e)
expToRM :: MidIRExpr -> CGM (Graph A.Asm O O, A.OperRM)
expToRM e = expTo' A.RM_M (expToM e)
            `mplus` expTo' A.RM_R (expToR e)

withNode :: MidIRExpr -> CGM MidIRExpr
withNode e = return e

expToI :: MidIRExpr -> CGM A.Imm32
expToI e = mcut $ msum rules
    where
      rules = [ do I.Lit pos i <- withNode e
                   guard $ checkIf32Bit i
                   return $ A.Imm32 $ fromIntegral i

              , do (I.LitLabel pos s) <- withNode e
                   return $ A.Imm32Label s 0
              ]

expToR :: MidIRExpr -> CGM (Graph A.Asm O O, A.Reg)
expToR e = mcut $ msum rules
    where
      rules = [ -- Rules for putting the value of the expression into
                -- a register
        
                -- a <- 0 is the same as a <- a xor a
                do I.Lit pos 0 <- withNode e
                   dr <- genTmpReg
                   return ( mkMiddle $ A.ALU_IRMtoR pos A.Xor
                                         (A.IRM_R $ dr) dr
                          , dr )
              , do I.Lit pos i <- withNode e
                   guard $ checkIf32Bit i
                   dr <- genTmpReg
                   let src = A.Imm32 $ fromIntegral i
                   return ( mkMiddle $ A.mov pos src dr
                          , dr )
              , do I.Lit pos i <- withNode e
                   dr <- genTmpReg
                   return ( mkMiddle $ A.Mov64toR pos (A.Imm64 i) dr
                          , dr )
              , do I.Var pos v <- withNode e
                   return ( GNil
                          , A.SReg $ show v )
              , do I.LitLabel pos s <- withNode e
                   dr <- genTmpReg
                   return ( mkMiddle $ A.mov pos (A.Imm32Label s 0) dr
                          , dr )
              , do I.Load pos exp <- withNode e
                   (g, m) <- expToMem exp
                   dr <- genTmpReg
                   return ( g
                            <*> mkMiddle (A.mov pos m dr)
                          , dr )
              , do I.UnOp pos I.OpNeg exp <- withNode e
                   (g, o) <- expToRM exp
                   dr <- genTmpReg
                   return ( g
                            <*> mkMiddle (A.MovIRMtoR pos (rmToIRM o) dr)
                            <*> mkMiddle (A.Neg pos (A.RM_R dr))
                          , dr )
              , do I.UnOp pos I.OpNot exp <- withNode e
                   (g, o) <- expToRM exp
                   dr <- genTmpReg
                   return ( g
                            <*> mkMiddle (A.MovIRMtoR pos (rmToIRM o) dr)
                            <*> mkMiddle (A.ALU_IRMtoR pos A.Xor
                                               (A.IRM_I $ A.Imm32 (1))
                                               dr)
                          , dr )
              , do I.BinOp pos op expa expb <- withNode e
                   guard $ op `elem` [I.OpAdd, I.OpSub]
                   let op' = fromJust $ lookup op [ (I.OpAdd, A.Add)
                                                  , (I.OpSub, A.Sub) ]
                   (ga, a) <- expToIRM expa
                   (gb, b) <- expToIRM expb
                   dr <- genTmpReg
                   return ( ga
                            <*> mkMiddle (A.MovIRMtoR pos a dr)
                            <*> gb
                            <*> mkMiddle (A.ALU_IRMtoR pos op' b dr)
                          , dr )
              , do I.BinOp pos op expa expb <- withNode e
                   guard $ op `elem` [ I.CmpLT, I.CmpGT, I.CmpLTE
                                     , I.CmpGTE, I.CmpEQ, I.CmpNEQ ]
                   let flag = cmpToFlag op
                   (gb, b) <- expToIR expb
                   (ga, a) <- expToRM expa
                   dr <- genTmpReg
                   true <- genTmpReg
                   return ( ga <*> gb
                            <*> mkMiddle (A.mov pos (A.Imm32 $
                                                      fromIntegral I.bTrue) true)
                            <*> mkMiddle (A.mov pos (A.Imm32 $
                                                      fromIntegral I.bFalse) dr)
                            <*> mkMiddle (A.Cmp pos b a)
                            <*> mkMiddle (A.CMovRMtoR pos flag
                                           (A.RM_R $ true) dr)
                          , dr )
              , do I.BinOp pos I.OpMul expa expb <- withNode e
                   b <- expToI expb
                   A.Imm32 b' <- return b
                   let logb' = log2 b'
                       log2 1 = 0
                       log2 n = 1 + log2 (n `div` 2)
                   guard $ b' > 0
                   guard $ b' == 2 ^ logb'
                   (ga, a) <- expToIRM expa
                   dr <- genTmpReg
                   return ( ga
                            <*> mkMiddles [ A.MovIRMtoR pos a dr
                                          , A.Shl pos (A.Imm8 $ fromIntegral logb') (A.RM_R dr) ]
                          , dr )
              , do I.BinOp pos I.OpMul expa expb <- withNode e
                   b <- expToI expb
                   (ga, a) <- expToRM expa
                   dr <- genTmpReg
                   return ( ga
                            <*> mkMiddle (A.IMulImm pos b a dr)
                          , dr )
              , do I.BinOp pos I.OpMul expa expb <- withNode e
                   (ga, a) <- expToIRM expa
                   (gb, b) <- expToRM expb
                   dr <- genTmpReg
                   return ( ga <*> gb
                            <*> mkMiddle (A.MovIRMtoR pos a dr)
                            <*> mkMiddle (A.IMulRM pos b dr)
                          , dr )
              , do I.BinOp pos I.OpDiv expa expb <- withNode e
                   (ga, a) <- expToIRM expa
                   (gb, b) <- expToRM expb
                   dr <- genTmpReg
                   return ( ga <*> gb
                            <*> mkMiddle (A.MovIRMtoR pos a (A.MReg A.RAX))
                            <*> mkMiddle (A.mov pos (A.Imm32 0) (A.MReg A.RDX))
                            <*> mkMiddle (A.IDiv pos b)
                            <*> mkMiddle (A.mov pos (A.MReg A.RAX) dr)
                          , dr )
              , do I.BinOp pos I.OpMod expa expb <- withNode e
                   (ga, a) <- expToIRM expa
                   (gb, b) <- expToRM expb
                   dr <- genTmpReg
                   return ( ga <*> gb
                            <*> mkMiddle (A.MovIRMtoR pos a (A.MReg A.RAX))
                            <*> mkMiddle (A.mov pos (A.Imm32 0) (A.MReg A.RDX))
                            <*> mkMiddle (A.IDiv pos b)
                            <*> mkMiddle (A.mov pos (A.MReg A.RDX) dr)
                          , dr )
              , do I.Cond pos cexp texp fexp <- withNode e
                   (gflag, flag) <- expToFlag cexp
                   (gt, t) <- expToRM texp
                   (gf, f) <- expToIRM fexp
                   dr <- genTmpReg
                   return ( gf <*> mkMiddle (A.MovIRMtoR pos f dr)
                            <*> gt <*> gflag
                            <*> mkMiddle (A.CMovRMtoR pos flag t dr)
                          , dr )
              ]

expToMem :: MidIRExpr -> CGM (Graph A.Asm O O, A.MemAddr)
expToMem e = mcut $ msum rules
    where
      rules = [ do I.LitLabel pos s <- withNode e
                   return ( GNil
                          , A.MemAddr Nothing (A.Imm32Label s 0) Nothing A.SOne )
              , do I.BinOp pos I.OpAdd expa expb <- withNode e
                   a <- expToI expa
                   (gb, b) <- expToR expb
                   return (gb, A.MemAddr (Just b) a Nothing A.SOne)
              , do I.BinOp pos I.OpAdd expa expb <- withNode e
                   (gb, b) <- expToR expb
                   (ga, a) <- expToR expa
                   return (ga <*> gb, A.MemAddr (Just a) (A.Imm32 0) (Just b) A.SOne)
              , do (g, r) <- expToR e
                   return (g, A.MemAddr (Just r) (A.Imm32 0) Nothing A.SOne)
              ]
expToM :: MidIRExpr -> CGM (Graph A.Asm O O, A.MemAddr)
expToM e@(I.Load _ exp) = mcut $ expToMem exp
expToM e = fail ("Mem not a load: " ++ show e)

expToFlag :: MidIRExpr -> CGM (Graph A.Asm O O, A.Flag)
expToFlag e = mcut $ msum rules
    where
      rules = [ do I.BinOp pos op expa expb <- withNode e
                   guard $ op `elem` [ I.CmpLT, I.CmpGT, I.CmpLTE
                                     , I.CmpGTE, I.CmpEQ, I.CmpNEQ ]
                   let flag = cmpToFlag op
                   (gb, b) <- expToIR expb
                   (ga, a) <- expToRM expa
                   return ( ga <*> gb
                            <*> mkMiddle (A.Cmp pos b a)
                          , flag )
              , do (g, r) <- expToRM e
                   return ( g
                            <*> mkMiddle (A.Cmp noPosition
                                               (A.IR_I $ A.Imm32 $
                                                 fromIntegral I.bFalse)
                                               r)
                          , A.FlagNE )
              ]


cmpToFlag :: I.BinOp -> A.Flag
cmpToFlag I.CmpLT = A.FlagL
cmpToFlag I.CmpLTE = A.FlagLE
cmpToFlag I.CmpGT = A.FlagG
cmpToFlag I.CmpGTE = A.FlagGE
cmpToFlag I.CmpEQ = A.FlagE
cmpToFlag I.CmpNEQ = A.FlagNE
cmpToFlag _ = error "not a comparison!"

lookupLabel (GMany _ g_blocks _) lbl = case mapLookup lbl g_blocks of
  Just x -> x
  Nothing -> error "ERROR"

labelToAsmOut :: Graph A.Asm C C -> (Label, Maybe Label) -> [String]
labelToAsmOut graph (lbl, mnlabel)
    = [show a]
      ++ (map (ind . show) bs)
      ++ mjmp
      ++ (if not (null children) && not fallthrough
          then nextJmp else [])
  where f :: (MaybeC C (n C O), [n O O], MaybeC C (n O C))
             -> (n C O, [n O O], n O C)
        f (JustC e, nodes, JustC x) = (e, nodes, x)
        (a, bs, c) = f (blockToNodeList block)
        block = lookupLabel graph lbl
        children = successors block
        ind = ("   " ++)
        fallthrough = case mnlabel of
                        Just l -> l == head (reverse children)
                        Nothing -> False
        nextJmp = [ind $ "jmp " ++ (show $ head $ reverse children)]
        mjmp :: [String]
        mjmp = case c of
                 A.Jmp _ _ -> []
                 _ -> [ind $ show c]

dfsSearch graph lbl visited = foldl recurseDFS visited (reverse $ successors block)
  where block = lookupLabel graph lbl
        recurseDFS v' nv = if nv `elem` v' then v' else dfsSearch graph nv (v' ++ [nv])
  
lowIRToAsm m = [ ".section .data" ]
               ++ newline
               ++ ["# fields"]
               ++ (concatMap showField (lowIRFields m))
               ++ newline
               ++ ["# strings"]
               ++ (concatMap showString (lowIRStrings m))
               ++ newline
               ++  [ ".globl main" 
                   , "main:"
                   , "call method_main"
                   , "movq $0, %rax"
                   , "ret" ]
               ++ newline
               ++ (concatMap (showMethod (lowIRGraph m)) (lowIRMethods m))
  where 
    newline = [""]
    showField (LowIRField pos name size)
        = [ name ++ ": .skip " ++ (show size) ++ ", 0\t\t# " ++ showPos pos ]
    showString (name, pos, str) = [ name ++ ":\t\t# " ++ showPos pos
                                , "   .asciz " ++ (show str) ]
    showMethod graph (I.Method pos name entry postenter)
        = [name ++ ":"]
          ++ concatMap (labelToAsmOut graph) (zip visited nvisited)
      where visited = dfsSearch graph entry [entry]
            nvisited = case visited of
                         [] -> []
                         _ -> map Just (tail visited) ++ [Nothing]
                                                 
lowIRToGraphViz m = "digraph name {\n"
                    ++ (showFields (lowIRFields m))
                    ++ (showStrings (lowIRStrings m))
                    ++ (concatMap showMethod (lowIRMethods m))
                    ++ I.graphToGraphViz show (lowIRGraph m)
                    ++ "}"
    where showMethod (I.Method pos name entry postenter)
              = name ++ " [shape=doubleoctagon,label="++show name++"];\n"
                ++ name ++ " -> " ++ show entry ++ ";\n"
          showField (LowIRField pos name size)
              = "{" ++ name ++ "|" ++ show size ++ "}"
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
