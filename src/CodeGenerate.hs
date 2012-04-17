{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables #-}

module CodeGenerate where

import CLI
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
import Text.Printf

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
instToAsm (I.DivStore pos d op expa expb)
    = do (ga, a) <- expToIRM expa
         (gb, b) <- expToRM expb
         return $ ga <*> gb
                  <*> mkMiddles [ A.MovIRMtoR pos a (A.MReg A.RAX)
                                , A.Cqo pos -- sign extend %rax into %rdx
                                , A.IDiv pos b
                                , A.mov pos (A.MReg src) (A.SReg $ show d)]
    where src = case op of
                  I.DivQuo -> A.RAX
                  I.DivRem -> A.RDX
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
                    <*> mkMiddle (A.Realign pos (max 0 ((length args) - 6)))
                    <*> genSetArgs pos vars
                    <*> mkMiddle (A.mov pos (A.Imm32 0) (A.MReg A.RAX))
                    <*> mkMiddle (A.Callout pos (length args) (A.Imm32Label name 0))
                    <*> mkMiddle (A.Unrealign pos)
                    <*> genResetSP pos args
                    <*> genPopRegs pos A.callerSaved
                    <*> mkMiddle (A.mov pos (A.MReg A.RAX) (A.SReg $ show d))
instToAsm (I.Branch pos l)
    = return $ mkLast $ A.Jmp pos (A.Imm32BlockLabel l 0)
instToAsm (I.CondBranch pos cexp tl fl)
    = do (g, flag) <- expToFlag cexp
         return $ g <*> (mkLast $ A.JCond pos flag (A.Imm32BlockLabel tl 0) fl)
instToAsm (I.Return pos fname Nothing)
    = return $ genPopRegs pos A.calleeSaved
               <*> (mkMiddle $ A.Leave pos)
               <*> (mkLast $ A.Ret pos False)
instToAsm (I.Return pos fname (Just exp))
    = do (g, irm) <- expToIRM exp
         return $ g <*> mkMiddle (A.MovIRMtoR pos irm (A.MReg A.RAX))
                    <*> genPopRegs pos A.calleeSaved
                    <*> (mkMiddle $ A.Leave pos)
                    <*> mkLast (A.Ret pos True)
instToAsm (I.Fail pos)
    = return $ mkMiddles [ A.mov pos (A.Imm32 1) (A.MReg A.RDI)
                         , A.mov pos (A.Imm32 0) (A.MReg A.RAX)
                         , A.Realign pos 0
                         , A.Callout pos 1 (A.Imm32Label "exit" 0) ]
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

                -- should use leaq for this!
--              , do (I.LitLabel pos s) <- withNode e
--                   return $ A.Imm32Label s 0
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
                   let mem = A.MemAddr Nothing (A.Imm32Label s 0) Nothing A.SOne
                   return ( mkMiddle $ A.Lea pos mem dr
                          , dr )
              , do I.Load pos exp <- withNode e
                   (g, m) <- expToMem exp
                   dr <- genTmpReg
                   return ( g
                            <*> mkMiddle (A.mov pos m dr)
                          , dr )
              , do I.UnOp pos I.OpNeg exp <- withNode e
                   (g, o) <- expToIRM exp
                   dr <- genTmpReg
                   return ( g
                            <*> mkMiddle (A.MovIRMtoR pos o dr)
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
              -- , do I.BinOp pos I.OpDiv expa expb <- withNode e
              --      (ga, a) <- expToIRM expa
              --      (gb, b) <- expToRM expb
              --      dr <- genTmpReg
              --      return ( ga <*> gb
              --               <*> mkMiddle (A.MovIRMtoR pos a (A.MReg A.RAX))
              --               <*> mkMiddle (A.mov pos (A.Imm32 0) (A.MReg A.RDX))
              --               <*> mkMiddle (A.IDiv pos b)
              --               <*> mkMiddle (A.mov pos (A.MReg A.RAX) dr)
              --             , dr )
              -- , do I.BinOp pos I.OpMod expa expb <- withNode e
              --      (ga, a) <- expToIRM expa
              --      (gb, b) <- expToRM expb
              --      dr <- genTmpReg
              --      return ( ga <*> gb
              --               <*> mkMiddle (A.MovIRMtoR pos a (A.MReg A.RAX))
              --               <*> mkMiddle (A.mov pos (A.Imm32 0) (A.MReg A.RDX))
              --               <*> mkMiddle (A.IDiv pos b)
              --               <*> mkMiddle (A.mov pos (A.MReg A.RDX) dr)
              --             , dr )
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

labelToAsmOut :: Bool -> Graph A.Asm C C -> (Label, Maybe Label) -> [String]
labelToAsmOut macmode graph (lbl, mnlabel)
    = [show a]
      ++ (map (show') bs)
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
        show' :: A.Asm O O -> String
        show' x = if macmode
                  then case x of
                         A.Callout pos args (A.Imm32Label s 0)
                             -> show $ A.Callout pos args (A.Imm32Label ("_" ++ s) 0)
                         A.Realign pos nstackargs
                             -> let code=[ A.mov pos (A.MReg A.RSP) (A.MReg A.R12)
                                         , A.ALU_IRMtoR pos A.Sub 
                                                        (A.IRM_I $ A.Imm32 16)
                                                        (A.MReg A.RSP)
                                         , A.ALU_IRMtoR pos A.And
                                                        (A.IRM_I $ A.Imm32 (-10))
                                                        (A.MReg A.RSP)
                                         , A.ALU_IRMtoR pos A.Sub
                                                        (A.IRM_I $ A.Imm32 $ fromIntegral corr)
                                                        (A.MReg A.RSP) ]
                                    corr=(nstackargs `mod` 2) * 8
                                in intercalate "\n" $ map (ind . show) code
                         A.Unrealign pos
                             -> show $ A.mov pos (A.MReg A.R12) (A.MReg A.RSP)
                         _ -> ind $ show x
                  else ind $ show x
        fallthrough = case mnlabel of
                        Just l -> l == head (reverse children)
                        Nothing -> False
        nextJmp = [ind $ "jmp " ++ (show $ head $ reverse children)]
        mjmp :: [String]
        mjmp = case c of
                 A.Jmp _ _ -> []
                 _ -> [ind $ show c]

dfsSearch :: (NonLocal n) => Graph n C C -> Label -> [Label] -> [Label]
dfsSearch graph lbl visited = foldl recurseDFS visited (reverse $ successors block)
  where block = lookupLabel graph lbl
        recurseDFS v' nv = if nv `elem` v' then v' else dfsSearch graph nv (v' ++ [nv])

lowIRToAsm :: LowIRRepr -> CompilerOpts -> [String]
lowIRToAsm m opts
    = [ ".data" ]
      ++ newline
      ++ ["# fields"]
      ++ (concatMap showField (lowIRFields m))
      ++ newline
      ++ ["# strings"]
      ++ (concatMap showString (lowIRStrings m))
      ++ newline
      ++  [ ".text"
          , ".globl main" 
          , ".globl _main" 
          , "main:"
          , "_main:"
          , "call method_main"
          , "movq $0, %rax"
          , "ret" ]
      ++ ["# methods"]
      ++ (concatMap (showMethod (macMode opts) (lowIRGraph m)) (lowIRMethods m))
  where 
    newline = [""]
    showField (LowIRField pos name size)
        = [ name ++ ": .space " ++ (show size) ++ ", 0\t\t# " ++ showPos pos ]
    showString (name, pos, str) = [ name ++ ":\t\t# " ++ showPos pos
                                , "   .asciz " ++ (show str) ]
    showMethod macmode graph (I.Method pos name entry postenter)
        = ["", name ++ ":"]
          ++ concatMap (labelToAsmOut macmode graph) (zip visited nvisited)
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

--- Map everything to C
class ShowC a where
    showC :: a -> String

instance ShowC Label where
    showC lbl = "label_" ++ (show lbl)

instance ShowC VarName where
    showC (I.MV s) = tail s

data ExprWrap v = EW (I.Expr v)
instance (ShowC v) => Show (ExprWrap v) where
    showsPrec _ (EW (I.Lit pos x)) = shows x
    showsPrec _ (EW (I.LitLabel pos lab)) = showString "(long)" . showString lab
    showsPrec _ (EW (I.Var pos v)) = showString $ showC v
    showsPrec _ (EW (I.Load pos expr)) = showString "*(long *)(" . showsPrec 0 (EW expr) . showString ")"
    showsPrec p (EW (I.UnOp pos op expr)) = showParen (p>0) (shows op . showString " " . showsPrec 1 (EW expr))
    showsPrec p (EW (I.BinOp pos op ex1 ex2))
        = showParen (p>0) (showsPrec 1 (EW ex1) . showString " " . shows op . showString " " . showsPrec 1 (EW ex2))
    showsPrec p (EW (I.Cond pos exc ex1 ex2))
        = showParen (p>0) (showsPrec 1 (EW exc)
                           . showString " ? " . showsPrec 1 (EW ex1)
                           . showString " : " . showsPrec 1 (EW ex2))

instance (ShowC v) => ShowC (I.Expr v) where
    showC = show . EW

showT :: (Show a) => a -> String
showT = tail . show

instance (ShowC v) => ShowC (I.Inst v e x) where
    showC (I.Label pos lbl)
        = printf "%s: // {%s}"
          (showC lbl) (showPos pos)
    showC (I.Enter pos lbl args)
        = printf "%s: // {%s}"
          (showC lbl) (showPos pos)
    showC (I.PostEnter pos lbl)
        = printf "%s: // {%s}"
          (showC lbl) (showPos pos)
    showC (I.Store pos var expr)
        = printf "%s = %s; // {%s}"
          (showC var) (showC expr) (showPos pos)
    showC (I.DivStore pos var op expr1 expr2)
        = printf "%s = (%s) %s (%s); // {%s}"
          (showC var) (showC expr1) (show op) (showC expr2) (showPos pos)
    showC (I.IndStore pos dest expr)
        = printf "*((long *)(%s)) = %s; // {%s}"
          (showC dest) (showC expr) (showPos pos)
    showC (I.Call pos dest name args)
        = printf "%s = %s(%s); // {%s}"
          (showC dest) name (intercalate ", " $ map showC args) (showPos pos)
    showC (I.Callout pos dest name args)
        = printf "%s = %s(%s); // {%s}"
          (showC dest) name (intercalate ", " $ map showC args) (showPos pos)
    showC (I.Branch pos lbl)
        = printf "goto %s; // {%s}"
          (showC lbl) (showPos pos)
    showC (I.CondBranch pos expr tlbl flbl)
        = printf "if (%s) // {%s}\n      goto %s;\n    else\n      goto %s;"
          (showC expr) (showPos pos) (showC tlbl) (showC flbl)
    showC (I.Return pos for mexpr)
        = printf "return %s; // {%s, %s}"
          (maybe "0" showC mexpr) for (showPos pos)
    showC (I.Fail pos)
        = printf "exit(1); // {%s}"
          (showPos pos)

variablesUsed :: Block I.MidIRInst C C -> S.Set I.VarName
variablesUsed block = S.fromList $ map fromJust $ filter isJust $ map getVar instrs
    where (_, instrs, _) = blockToNodeList block
          getVar :: (I.Inst v e x) -> Maybe v
          getVar (I.Store _ var _) = Just var
          getVar (I.DivStore _ var _ _ _) = Just var
          getVar (I.Call _ var _ _) = Just var
          getVar (I.Callout _ var _ _) = Just var
          getVar _ = Nothing

extractInsts :: (MaybeC C (n C O), [n O O], MaybeC C (n O C))
                -> (n C O, [n O O], n O C)
extractInsts (JustC e, nodes, JustC x) = (e, nodes, x)

extractArgs :: Block I.MidIRInst C C -> [VarName]
extractArgs block =
    case instTriple of
        (I.Enter _ _ args, _, _) -> args
        _ -> error "shouldn't be extracting args here :-O"
    where instTriple = extractInsts $ blockToNodeList block

hasReturn :: Block I.MidIRInst C C -> Bool
hasReturn block =
    case instTriple of
        (_, _, I.Return _ _ returnVal) -> isJust returnVal
        _ -> False
    where instTriple = extractInsts $ blockToNodeList block

midIRToC :: I.MidIRRepr -> String
midIRToC m = "#include <stdio.h>\n#include <stdlib.h>\n"
             ++ (showFields (I.midIRFields m))
             ++ (showStrings (I.midIRStrings m))
             -- ++ "void main()\n{\n"
             ++ (showMethods (I.midIRMethods m))
             -- ++ graphToC showC (graph)
             -- ++ "}"
 
    where graph = I.midIRGraph m
          showMethod (I.Method pos name entry postenter)
              = printf "%s %s(%s)\n{\n%s\n\n%s\n}"
                returnType cName argString varString instString
              where visited = dfsSearch graph entry [entry]
                    nvisited = case visited of
                                   [] -> []
                                   _ -> map Just (tail visited) ++ [Nothing]
                    entryBlock = lookupLabel graph entry
                    args = extractArgs entryBlock
                    argString = intercalate ", " (map (("long " ++) . showC) args)
                    varSet = foldl1 S.union $ map (variablesUsed . lookupLabel graph) visited
                    vars = S.toList (S.difference varSet $ S.fromList args)
                    varString :: String
                    varString = 
                        case vars of
                            [] -> "  // no locals"
                            _ -> printf "  long %s;" (intercalate ", " (map showC vars))
                    instString = (intercalate "\n" $ intercalate [""] $ map (labelToC graph) (zip visited nvisited))
                    returnType = "long"
                    cName
                        | name == "method_main" = "main"
                        | otherwise = name
          showMethods methods = "/* begin methods */\n" 
                                ++ (intercalate "\n\n" $ map showMethod methods)
          showField (I.MidIRField pos name msize)
              = "long " ++ name ++ (showSize msize) ++ ";\n"
          showSize (Just n) = printf "[%s]" (show n)
          showSize (Nothing) = "[1]"
          showFields fields = "/* begin fields */\n" 
                              ++ (concatMap showField fields) ++ "\n"
          showString (name, pos, str) = printf "char *%s = %s;\n" name (show str)
          showStrings strings = "/* begin strings */\n"
                                ++ (concatMap showString strings) ++ "\n"

labelToC :: Graph I.MidIRInst C C -> (Label, Maybe Label) -> [String]
labelToC graph (lbl, mnlabel)
    = ["  " ++ (showC a) ++ " // (a)"]
      ++ (map (show') bs)
      ++ mjmp
      ++ (if not (null children) && not fallthrough
          then nextJmp else [])
  where (a, bs, c) = extractInsts (blockToNodeList block)
        block = lookupLabel graph lbl
        children = successors block
        ind = ("    " ++)
        show' :: I.MidIRInst e x -> String
        show' x = (ind $ showC x) ++ " // (bs)"
        fallthrough = case mnlabel of
                        Just l -> l == head (reverse children)
                        Nothing -> False
        nextJmp = [ind $ "goto " ++ (showC $ head $ reverse children) ++ ";"]
        mjmp :: [String]
        mjmp = case c of
                 _ -> [(ind $ showC c) ++ " // (c)"]
