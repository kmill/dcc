module SemanticCheck where

import AST
import Unify
import qualified Data.Map as Map
import Control.Applicative
import Control.Monad

doSemanticCheck :: DProgram -> IO ()
doSemanticCheck ast = putStrLn "Hi"

data LexicalEnv = LexicalEnv
    { lexicalBindings :: Map.Map String DUTerm
    , parentEnv :: Maybe LexicalEnv }
    
envLookup :: String -> LexicalEnv -> Maybe DUTerm
envLookup name lenv = Map.lookup name e
                      `mplus` ((parentEnv lenv) >>= envLookup name)
    where e = lexicalBindings lenv

envBind :: String -> DUTerm -> LexicalEnv -> LexicalEnv
envBind name val lenv = lenv { lexicalBindings=Map.insert name val e }
    where e = lexicalBindings lenv

data DUType = DUInt
            | DUBool
            | DUVoid
            | DUArray (Maybe Int)
            | DUFunc
              deriving (Eq, Show)

type DUTerm = Term DUType


testunify = let t1 = Term DUInt []
                t2 = Var (UVar "x" 0)
                t3 = Term DUBool []
            in unify t1 t2
               
testunify2 = do let t1 = Term DUInt []
                t2 <- Var <$> genvar "y"
                t2 <- Var <$> genvar "y"
                unify t1 t2
             
checkDProgram :: LexicalEnv -> DProgram -> Unifier ()
checkDProgram env (DProgram _ fdecls mdecls)
    = do sequence_ [checkFieldDecl env f | f <- fdecls]
         
checkFDecl :: LexicalEnv -> FieldDecl -> Unifier ()
checkFDecl env (FieldDecl _ t vars)
    = do sequence_ [checkvar v | v <- vars]
    where
      getDUType DInt = DUInt
      getDUType DBool = DUBool
      checkvar (PlainVar _ t)
          = envBind (tokenString t) (getDUType t) env