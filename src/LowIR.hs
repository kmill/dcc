module LowIR where

import IR
--import MidIR
import Data.Maybe
import Control.Monad
import Control.Monad.State
import Data.Graphs
import AST (PP(..), SourcePos)
import qualified Data.Map as Map
import Text.PrettyPrint.HughesPJ
import Data.List

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
         return $ LowIRMethod pos retp name (length args) lir

basicBlockToLowIR :: Globals -> MidBasicBlock -> State LowIRState LowBasicBlock
basicBlockToLowIR glob (BasicBlock code test testpos)
    = do (testcode, test') <- testToLowIR glob testpos test
         return $ BasicBlock testcode test' testpos

varToLoadCode :: Globals -> SourcePos -> String
              -> State LowIRState ([LowIRInst], LowOper)
varToLoadCode g pos s
    = case s `elem` g of
        True -> do r <- genReg
                   return $ ( [LoadMem pos r (MemAddrPtr s)]
                            , OperReg r)
        False -> do r <- getReg s
                    return ([], OperReg r)

operToLoadCode :: Globals -> SourcePos -> MidOper
               -> State LowIRState ([LowIRInst], LowOper)
operToLoadCode g pos (OperVar s) = varToLoadCode g pos s
operToLoadCode g pos (OperConst v) = return $ ([], LowOperConst v)

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
             return (code, IRReturn $ Just oper')
      IRReturn Nothing -> return ([], IRReturn Nothing)
      IRTestFail s -> return ([], IRTestFail s)

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
    pp (LowIRMethod pos retp name nargs ir)
        = text ("{" ++ show pos ++ "}")
           $+$ (if retp then text "ret" else text "void") <+> text name
           <+> text (show nargs)
           $+$ (text $ "start = " ++ show (startVertex ir))
           $+$ (nest 3 (vcat [showVertex v | v <- labels ir]))
        where showVertex (i,bb) = text (show i)
                                   <+> (nest 3 (pp bb))
                                   $+$ (nest 5 (vcat (map showEdge outedges)))
                  where outedges = adjEdges ir i
                        showEdge (b,y) = text (show b ++ " -> " ++ show y)
                        

lowIRtoGraphViz m = "digraph name {\n"
                    ++ (showFields (lowIRFields m))
                    ++ (showStrings (lowIRStrings m))
                    ++ (concatMap showMethod (lowIRMethods m))
                    ++ "}"
  where showMethod (LowIRMethod pos retp name nargs g)
            = graphToGraphVizSubgraph g (name ++ "_")
              (name ++ " [shape=doubleoctagon,label="++show mlabel++"];\n"
              ++ name ++ " -> " ++ name ++ "_" ++ show (startVertex g) ++ ";\n")
            where mlabel = (if retp then "ret " else "void ")
                           ++ name ++ " " ++ show nargs
        showField (LowIRField pos name size)
            = "{" ++ name ++ "|" ++ show size ++ " bytes}"
        showFields fields = "_fields_ [shape=record,label=\"fields|{"
                            ++ intercalate "|" (map showField fields)
                            ++ "}\"];\n"
        showStrings strings = "_strings_ [shape=record,label=\"strings|{"
                              ++ intercalate "|" (map showString strings)
                              ++ "}\"];\n"
        showString (name, pos, str)
            = "{" ++ name ++ "|" ++ show str ++ "|" ++ show pos ++ "}"