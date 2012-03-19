module RegisterAllocator where 

import qualified Data.Map as Map 
import IR 
import Control.Monad.State
import Data.Graphs
import AST (SourcePos)

-- | The State used to maintain stack consistency while removing symbolic registers
data DestroySymbRegState = DestroySymbRegState { nextStackOffset :: Int 
                                               , symbolMappings :: Map.Map RegName MemAddr } 

lookupSymbMapping :: RegName -> DestroySymbRegState -> Maybe MemAddr 
lookupSymbMapping reg currentState = Map.lookup reg $ symbolMappings currentState 

insertSymbMapping :: RegName -> DestroySymbRegState -> (MemAddr, DestroySymbRegState) 
insertSymbMapping reg currentState = case lookupSymbMapping reg currentState of 
                                       Just addr -> (addr, currentState) 
                                       Nothing -> let offset = nextStackOffset currentState 
                                                      addr = MemAddr (X86Reg RBP) offset Nothing 0 
                                                      oldMap = symbolMappings currentState 
                                                      newMap = Map.insert reg addr oldMap 
                                                      newState = currentState { symbolMappings = newMap 
                                                                              , nextStackOffset = offset + 8 } 
                                                  in (addr, newState) 

-- | The Symbolic Registers are the greatest evil the world has ever known. We must destroy them 
-- | Go hero, take forth this sacred weapon and fulfill your destiny. 
destroySymbRegs :: LowIRRepr -> LowIRRepr 
destroySymbRegs (LowIRRepr fields strings methods) 
    = LowIRRepr fields strings methods' 
    where methods' = map methodDestroySymbRegs methods


methodDestroySymbRegs :: LowIRMethod -> LowIRMethod
methodDestroySymbRegs (LowIRMethod pos retp name numArgs _ lir) 
    = LowIRMethod pos retp name numArgs localsSize lir'
    where (lir', finalState) = runState (mapGM basicBlockDestroySymbRegs lir) initState  
          localsSize = fromIntegral $ (nextStackOffset finalState) - 8
          initState = DestroySymbRegState { nextStackOffset = 8
                                          , symbolMappings = Map.empty }

basicBlockDestroySymbRegs :: LowBasicBlock -> State DestroySymbRegState LowBasicBlock
basicBlockDestroySymbRegs (BasicBlock code test testpos) 
    = do code' <- mapM statementDestroySymbRegs code 
         (testcode, test') <- testDestroySymbRegs testpos test 
         return $ BasicBlock (join code' ++ testcode) test' testpos 
         
testDestroySymbRegs :: SourcePos -> IRTest LowOper -> State DestroySymbRegState ([LowIRInst], IRTest LowOper)
testDestroySymbRegs pos test 
    = case test of 
        IRTestBinOp binOp oper1 oper2 -> 
            do (loadOper1, oper1') <- operDestroySymbRegs pos oper1 (X86Reg R10) 
               (loadOper2, oper2') <- operDestroySymbRegs pos oper2 (X86Reg R11) 
               let newCode = loadOper1 ++ 
                             loadOper2
                   newTest = IRTestBinOp binOp oper1' oper2' 
               return (newCode, newTest)
        IRTest oper ->
            do (loadOper, oper') <- operDestroySymbRegs pos oper (X86Reg R10) 
               let newCode = loadOper
                   newTest = IRTest oper'
               return (newCode, newTest)
        IRTestNot oper -> 
            do (loadOper, oper') <- operDestroySymbRegs pos oper (X86Reg R10) 
               let newCode = loadOper 
                   newTest = IRTestNot oper' 
               return (newCode, newTest) 
        IRReturn (Just oper) -> 
            do (loadOper, oper') <- operDestroySymbRegs pos oper (X86Reg R10) 
               let newCode = loadOper
                   newTest = IRReturn $ Just oper' 
               return (newCode, newTest)
        _ -> return ([], test) 

getStackLoc :: RegName -> State DestroySymbRegState MemAddr 
getStackLoc reg@(SymbolicReg _) = do symbolState <- get 
                                     let (memAddr, newState) = insertSymbMapping reg symbolState
                                     put newState 
                                     return memAddr 
getStackLoc reg@(X86Reg r) = error "Attempted to allocate space on the stack for a concrete register :-{"

-- | Function that removes symbolic registers from a low oper if necessary 
-- | Also produces a list of statements needed to load the oper value into an appropriate temp register
operDestroySymbRegs :: SourcePos -> LowOper -> RegName -> State DestroySymbRegState ([LowIRInst], LowOper) 
operDestroySymbRegs pos (OperReg reg@(SymbolicReg i)) tmpReg
    = do memAddr <- getStackLoc reg
         let loadCodes = [LoadMem pos tmpReg memAddr]
         return (loadCodes, OperReg tmpReg)
operDestroySymbRegs pos oper tmpReg = return ([], oper) 

-- | Function that removes symbolic registers from destination registers 
-- | Instead, it takes in a temp register (used in place of the destination register) and produces 
-- | code to move the value in the temp register to the appropriate memlocation of the symbolic register
destRegDestroySymbRegs :: SourcePos -> RegName -> RegName -> State DestroySymbRegState [LowIRInst] 
destRegDestroySymbRegs pos reg@(SymbolicReg _) tmpReg
    = do memAddr <- getStackLoc reg 
         let storeCodes = [StoreMem pos memAddr (OperReg tmpReg)]
         return storeCodes
destRegDestroySymbRegs pos _ tmpReg = return []

statementDestroySymbRegs :: LowIRInst -> State DestroySymbRegState [LowIRInst] 
statementDestroySymbRegs inst =
    case inst of 
      RegBin pos dest op oper1 oper2 -> 
          do (loadOper1, oper1') <- operDestroySymbRegs pos oper1 (X86Reg R10)
             (loadOper2, oper2') <- operDestroySymbRegs pos oper2 (X86Reg R11) 
             storeVal <- destRegDestroySymbRegs pos dest (X86Reg RAX)
             let newCode = loadOper1 ++
                           loadOper2 ++ 
                           [(RegBin pos (X86Reg RAX) op oper1' oper2')] ++
                           storeVal
             return newCode 
      RegUn pos dest op oper -> 
          do (loadOper, oper') <- operDestroySymbRegs pos oper (X86Reg R10) 
             storeVal <- destRegDestroySymbRegs pos dest (X86Reg R11) 
             let newCode = loadOper ++ 
                           [RegUn pos (X86Reg R11) op oper'] ++ 
                           storeVal 
             return newCode 
      RegVal pos dest oper -> 
          do (loadOper, oper') <- operDestroySymbRegs pos oper (X86Reg R10)
             storeVal <- destRegDestroySymbRegs pos dest (X86Reg R11) 
             let newCode = loadOper ++ 
                           [RegVal pos (X86Reg R11) oper'] ++ 
                           storeVal 
             return newCode 
      RegCond pos dest cmp cmp1 cmp2 src -> 
          do (loadCmp1, cmp1') <- operDestroySymbRegs pos cmp1 (X86Reg R10) 
             (loadCmp2, cmp2') <- operDestroySymbRegs pos cmp2 (X86Reg R11) 
             (loadCmpSrc, src') <- operDestroySymbRegs pos src (X86Reg RAX) 
             storeVal <- destRegDestroySymbRegs pos dest (X86Reg RBX) 
             let newCode = loadCmp1 ++
                           loadCmp2 ++ 
                           loadCmpSrc ++ 
                           [RegCond pos (X86Reg RBX) cmp cmp1' cmp2' src'] ++ 
                           storeVal
             return newCode 
      RegPush pos oper -> 
          do (loadOper, oper') <- operDestroySymbRegs pos oper (X86Reg R10) 
             let newCode = loadOper ++ 
                           [RegPush pos oper'] 
             return newCode 
      StoreMem pos addr oper -> 
          do (loadOper, oper') <- operDestroySymbRegs pos oper (X86Reg R10) 
             let newCode = loadOper ++ 
                           [StoreMem pos addr oper']
             return newCode
      LoadMem pos dest addr -> 
          do storeVal <- destRegDestroySymbRegs pos dest (X86Reg R10) 
             let newCode = [LoadMem pos (X86Reg R10) addr] ++
                           storeVal
             return newCode 
      LowCall pos name numArgs ->
          do return $ [LowCall pos name numArgs]
      LowCallout pos name numArgs -> 
          do return $ [LowCall pos name numArgs]



