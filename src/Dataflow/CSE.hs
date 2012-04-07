
module Dataflow.CSE where 

import Compiler.Hoopl
import IR2

-- | I'm going to be sticking an existing graph into this whole thing

-- | 1. Need to define a fact type (map of available expressions?)
-- | This is also a lattice. So I'll need to be careful about defining top and bottom as well.

-- | 2. Need to define a transfer function 

-- | 3. Need to define a rewrite rule

-- | Looks like the nodes are the Inst v e x type

-- | Can look directly at the constant propagation examples to get this working. 


-- | Use analyzeAndRewriteFwdBody to actually rewrite the graph once everything is well defined


-- | Constant Propagation Example Code to Draw from

type LitVal = (SourcePos, Int64)

-- Type and definition of the lattice
-- Need to figure out what "Var" Corresponds to 
type ConstFact = Map.Map VarName (WithTop LitVal)
constLattice :: DataflowLattice ConstFact
constLattice = DataFlowLattice { fact_bot = Map.empty 
                               , fact_join = joinMaps (extendJoinDomain constFactAdd) }
    where constFactAdd _ (OldFact old) (NewFact new) = if new == old then (NoChange, PElem new)
                                                       else (SomeChange, Top)

initFact :: [VarName] -> ConstFact 
initFact vars = Map.fromList $ [(v, Top) | v <- vars]

-- Analysis: variable equals a literal constant
varHasLit :: FwdTransfer MidIRInst ConstFact
varHasLit = mkFTransfer ft
    where
      ft :: MidIRInst e x -> ConstFact -> Fact x ConstFact
      ft (Label _) f = f
      ft (Store _ x (Lit pos k)) f = Map.insert x (PElem (pos, k)) f
      ft (Store _ x _) f = Map.insert x Top f
      ft (CondStore _ x _ _)  f = Map.insert x Top f 
      ft (IndStore _ _ _) f = f
      ft (Spill _ _ x) f = Map.insert x Top f
      ft (UnSpill _ _ _) f = f
      ft (Call _ _ _ _) f = f
      ft (Callout _ _ _ _) f = f
      ft (Branch _ l) f = mapSingleton l f
      ft (CondBranch _ (Var pos x) tl fl) f 
          = mkFactBase constLattice [ (tl, Map.insert x (PElem (pos, -1)) f)
                                    , (fl, Map.insert x (PElem (pos, 0)) f) ]
      ft (CondBranch _ _ tl fl) f 
          = mkFactBase constLattice [ (tl, f)
                                    , (fl, f) ]
      ft (Return _ _) f = mapEmpty
      ft (Fail _) f = mapSingleton l f

-- Rewrite function: replace constant variables
constProp :: forall m. FuelMonad m => FwdRewrite m MidIRInst ConstFact
constProp = mkFRewrite cp 
    where 
      cp :: MidIRInst e x -> ConstFact -> m (Maybe (Graph MidIRInst e x))
      cp node f 
             = return $ liftM insnToG $ mapVN (lookup f) node
      mapVN :: (VarName -> Maybe Expr) -> MaybeChange (Node e x) 
      mapVN = mapEN . mapEE . mapVE

      lookup :: ConstFact -> VarName -> Maybe Expr
      lookup f x = case Map.lookup x f of 
                     Just (PElem (pos, v)) -> Just $ Lit pos v
                     _ -> Nothing


type Node = MidIRInst 
type MaybeChange a = a -> Maybe a 
mapVE :: (VarName -> Maybe Expr) -> MaybeChange Expr
mapEE :: MaybeChange Expr -> MaybeChange Expr
mapEN :: MaybeChange Expr -> MaybeChange (Node e x) 
mapVN :: (VarName -> Maybe Expr) -> MaybeChange (Node e x)

mapVN = mapEN . mapEE . mapVE

mapVE f (VarName v) = f v 
mapVE _ _ = 