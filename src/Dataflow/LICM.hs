{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, TypeFamilies #-}
module Dataflow.LICM where

import Dataflow.OptSupport
import Dataflow.DeadCode
import DataflowTypes
import LoopAnalysis
import Parallelize(compare', MidIRMap, getBlock)
import AST(SourcePos)
import Compiler.Hoopl
import IR
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe(catMaybes, fromMaybe, isJust)
import Debug.Trace
import Control.Monad.Trans.State.Lazy

tr :: String -> a -> a
tr = trace
--tr = id
ts :: (Show a) => a -> b -> b
ts = tr . show
t :: (Show a) => a -> a
t x = ts x x
tt :: (Show a, Show b) => a -> b -> b
tt x y = ts (x, y) y

data Movable = Mov | Immov
    deriving (Eq, Ord, Show)
movJoin :: Movable -> Movable -> Movable
movJoin Mov Mov = Mov
movJoin _ _ = Immov

data (Ord v) => SInst v
    = SStore SourcePos v (Expr v)
    | SDivStore SourcePos v DivOp (Expr v) (Expr v)
    | SIndStore SourcePos (Expr v) (Expr v)
    | SOtherInst
      deriving (Eq, Ord)

instance (Show v, Ord v) => Show (SInst v) where
    show i = show $ unStoreInst i

storeInst :: (Ord v) => Inst v e x -> SInst v
storeInst (Store pos var expr) = SStore pos var expr
storeInst (DivStore pos var op expr1 expr2) = SDivStore pos var op expr1 expr2
storeInst (IndStore pos dest src) = SIndStore pos dest src
storeInst _ = SOtherInst

unStoreInst :: (Ord v) => SInst v -> Maybe (Inst v O O)
unStoreInst (SStore pos var expr) = Just $ Store pos var expr
unStoreInst (SDivStore pos var op expr1 expr2) = Just $ DivStore pos var op expr1 expr2
unStoreInst (SIndStore pos dest src) = Just $ IndStore pos dest src
unStoreInst SOtherInst = Nothing

type MSInst = SInst VarName

-- Set of instructions which can be moved to this point
type MotionMap = M.Map MSInst Movable
type MotionFact = (MotionMap, Live)
motionLattice :: DataflowLattice MotionFact
motionLattice = DataflowLattice { fact_name = "Code Motion Lattice"
                                , fact_bot = emptyMotionFact
                                , fact_join = intersectFacts }
    where intersectFacts :: Label -> OldFact MotionFact -> NewFact MotionFact -> (ChangeFlag, MotionFact)
          intersectFacts l (OldFact (oldMap, oldLive)) (NewFact (newMap, newLive))
              = (c, (resMap', resLive))
              where c = changeIf $ setBool || (changeBool lc)
                    setBool = not $ resMap' == oldMap
                    -- instruction survives if variable is in newMap or is dead
                    resMap = M.unionWith movJoin (M.intersectionWith movJoin oldMap newMap) (M.filterWithKey (isDeadIn oldLive) newMap) -- (trace (show newMap) newMap))
                    resMap'
                        | killIndStores = filterKey (not . isIndStore) resMap
                        | otherwise = resMap
                    killIndStores = filterKey isIndStore oldMap == filterKey isIndStore resMap
                    isDeadIn :: Live -> MSInst -> Movable -> Bool
                    isDeadIn live (SStore _ var _) _ = not $ S.member var live
                    isDeadIn live (SDivStore _ var _ _ _) _ = not $ S.member var live
                    isDeadIn _ _ _ = False
                    (lc, resLive) = fact_join liveLattice l (OldFact oldLive) (NewFact newLive)
                    changeBool SomeChange = True
                    changeBool NoChange = False

emptyMotionFact :: MotionFact
emptyMotionFact = (M.empty, S.empty)

exprDepend :: (Ord v) => Expr v -> M.Map v Movable
exprDepend (Var _ v) = M.singleton v Mov
exprDepend (Load _ expr) = exprDepend expr
exprDepend (UnOp _ _ expr) = exprDepend expr
exprDepend (BinOp _ _ expr1 expr2) = M.unionsWith movJoin $ map exprDepend $ [expr1, expr2] 
exprDepend (Cond _ exprc expr1 expr2)
    = M.unionsWith movJoin $ map exprDepend $ [exprc, expr1, expr2]
exprDepend _ = M.empty

instDepend :: (Ord v) => SInst v -> M.Map v Movable
instDepend (SStore _ _ expr) = exprDepend expr
instDepend (SDivStore _ _ _ expr1 expr2) = M.unionsWith movJoin $ map exprDepend $ [expr1, expr2]
instDepend (SIndStore _ expr1 expr2) = M.unionsWith movJoin $ map exprDepend $ [expr1, expr2]
instDepend SOtherInst = M.empty

decompose :: (IsMap m) => m (a, b) -> (m a, m b)
decompose m = (mapMap fst m, mapMap snd m)

pairBwdTransfer :: BwdTransfer n f -> BwdTransfer n f' -> BwdTransfer n (f, f')
pairBwdTransfer bt1 bt2 = mkBTransfer3 (a btCO1 btCO2) (a btOO1 btOO2) btOC
    where a :: (a -> b -> d) -> (a -> c -> e) -> a -> (b, c) -> (d, e)
          a btex1 btex2 i (f1, f2) = (btex1 i f1, btex2 i f2)
          btOC i f = (btOC1 i f1, btOC2 i f2)
              where (f1, f2) = decompose f
          (btCO1, btOO1, btOC1) = getBTransfer3 bt1
          (btCO2, btOO2, btOC2) = getBTransfer3 bt2

isIndStore :: (Ord v) => SInst v -> Bool
isIndStore SIndStore{} = True
isIndStore _ = False

filterKey :: (Ord k) => (k -> Bool) -> M.Map k v -> M.Map k v
filterKey f = M.filterWithKey (\a _ -> f a) 

motionMapTransfer :: BwdTransfer MidIRInst MotionMap
motionMapTransfer = mkBTransfer3 btCO' btOO btOC
    where btCO' n f = ts (n, btCO n f) $ btCO n f
          btCO :: MidIRInst C O -> MotionMap -> MotionMap
          btCO i@(Enter _ _ args) f = invalidateList args f
          btCO _ f = f

          btOO :: MidIRInst O O -> MotionMap -> MotionMap
          btOO i@(Store _ var expr) f
             = invalidate var (M.insert (storeInst i) Mov f)
             --  = (\res -> trace ("store " ++ (show i) ++ " with lattice " ++ (show f) ++ "\n" ++ (show res) ++ "\n") res) $ invalidate var (S.insert (storeInst i) f)
          btOO i@(DivStore _ var _ expr1 expr2) f
              = invalidate var (M.insert (storeInst i) Mov f)
          btOO i@(IndStore _ _ _) f = M.insert (storeInst i) Mov f
          btOO (Call _ var _ _) f = invalidate var f
          btOO (Callout _ var _ _) f = invalidate var f

          btOC :: MidIRInst O C -> FactBase MotionMap -> MotionMap
          btOC Parallel{} _ = error "LICM should come before parallelization!"
          btOC n fb = M.unionsWith movJoin $ map (\l -> mapFindWithDefault M.empty l fb) $ successors n

          invalidate :: VarName -> MotionMap -> MotionMap
          invalidate var fact = trace ("invalidating " ++ (show var) ++ " in " ++ (show fact)) filterMov (not . dependsOn var) fact'
              where fact'
                        | killIndStores = filterMov (not . isIndStore) fact
                        | otherwise = fact
                    killIndStores = M.null $ filterKey (dependsOn var) indStores
                    indStores = filterKey isIndStore fact
                    dependsOn :: VarName -> MSInst -> Bool
                    dependsOn var n = M.member var $ tt n $ instDepend n
                    filterMov :: (MSInst -> Bool) -> MotionMap -> MotionMap
                    filterMov f = M.mapWithKey change
                        where change :: MSInst -> Movable -> Movable
                              change a b
                                  | f a = b
                                  | otherwise = tr "FOUND IMMOV" Immov

          invalidateList :: [VarName] -> MotionMap -> MotionMap
          invalidateList vars initial = foldr invalidate initial vars

motionTransfer :: BwdTransfer MidIRInst MotionFact
motionTransfer = pairBwdTransfer motionMapTransfer liveness

motionRewrite :: forall m . FuelMonad m => BwdRewrite m MidIRInst MotionFact
motionRewrite = noBwdRewrite
{-
motionRewrite loops = trace (show loops) $ mkBRewrite3 idRewr idRewr r
    where idRewr :: MidIRInst e x -> Fact x MotionFact -> m (Maybe (Graph MidIRInst e x))
          idRewr i _ = return Nothing
          r :: MidIRInst O C -> Fact C MotionFact -> m (Maybe (Graph MidIRInst O C))
          -- We drop things off only right before loop headers
          r i@(Branch _ lbl) facts
              | S.notMember lbl $ S.map loop_header loops = return Nothing 
              | otherwise
                  = case getInstrs facts of 
                      [] -> return Nothing
                      xs -> return $ Just $ (mkMiddles xs) <*> (mkLast i)
          r i _ = return Nothing
          getInstrs :: FactBase MotionFact -> [MidIRInst O O]
          getInstrs = catMaybes . map unStoreInst . S.toList . S.unions . mapElems . mapMap fst
-}

compareBasic :: BasicLoop -> BasicLoop -> Ordering
compareBasic loop1 loop2 =
    case compareBodies of
        EQ -> compare loop1 loop2
        res -> res
    where compareBodies = compare (S.size $ basicBody loop1) (S.size $ basicBody loop2)

type SM a = State (S.Set MSInst) a
-- should move loops in reverse order, state keeps track of which instructions have already been moved
doLICM :: S.Set BasicLoop -> FactBase MotionFact -> Graph MidIRInst C C -> Graph MidIRInst C C
doLICM loops facts graph = evalState monadic S.empty
    where monadic = foldl (>>=) (return graph) $ map (motionLoop facts) $ reverse $ L.sortBy compareBasic $ S.toList loops

motionLoop :: FactBase MotionFact -> BasicLoop -> Graph MidIRInst C C -> SM (Graph MidIRInst C C)
motionLoop facts loop graph = do
    alreadyMoved <- get
    let toMove = naiveToMove S.\\ alreadyMoved
        toMoveList = instList toMove
        predBlock' = blockOfNodeList (entry, middle ++ toMoveList, exit)
        blockMap' = mapInsert (basicHeaderPred loop blockMap) predBlock' blockMap
        -- remove blocks we've moved
        filterBlock :: Label -> Block MidIRInst C C -> Block MidIRInst C C
        filterBlock lbl block
            | S.member lbl $ basicBody loop
                = let (bentry, bnodes, bexit) = blockToNodeList block
                      notToMove :: MidIRInst O O -> Bool
                      notToMove n = not $ S.member (storeInst n) toMove
                      bnodes' = filter notToMove bnodes
                  in blockOfNodeList (bentry, bnodes', bexit)
            | otherwise = block
        blockMap'' = mapMapWithKey filterBlock blockMap'
    put $ S.union alreadyMoved toMove
    return $ GMany NothingO blockMap'' NothingO
    where GMany _ blockMap _ = graph
          isMov :: Movable -> Bool
          isMov Mov = True
          isMov Immov = False
          naiveToMove = M.keysSet $ M.filter isMov $ t $ fst fact
          fact = mapFindWithDefault (error "couldn't find label for licm") (basicHeader loop) (t facts)
          predBlock = basicHeaderPredBlock (t loop) blockMap
          (entry, middle, exit) = blockToNodeList predBlock
          instList :: S.Set MSInst -> [MidIRInst O O]
          instList = catMaybes . map unStoreInst . S.toList

basicHeaderPred :: BasicLoop -> MidIRMap -> Label
basicHeaderPred bloop blockMap
    = head $ map fst $ filter (elem lbl . successors . snd) bloopList
    where lbl = basicHeader bloop
          bloopList = filter (\(l, b) -> S.notMember l $ basicBody bloop) list
          list = mapToList blockMap

basicHeaderPredBlock :: BasicLoop -> MidIRMap -> Block MidIRInst C C
basicHeaderPredBlock bloop blockMap = getBlock (basicHeaderPred bloop blockMap) blockMap
