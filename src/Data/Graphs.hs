{-# LANGUAGE ParallelListComp #-}

-- | from
-- http://www.haskell.org/haskellwiki/The_Monad.Reader/Issue5/Practical_Graph_Handling

module Data.Graphs where

import Data.Array
import Control.Monad.ST
import Data.STRef
import qualified Data.Map as Map
import Data.Maybe

type Vertex = Int
type Table a = Array Vertex a
type Graph e = Table [(e, Vertex)]
type Bounds  = (Vertex, Vertex)
type Edge e = (Vertex, e, Vertex)

type Labeling a = Vertex -> a
data LabGraph n e = LabGraph (Graph e) (Labeling n)
 
vertices (LabGraph gr _) = indices gr
 
labels (LabGraph gr l) = map l (indices gr)


unfoldG :: (Ord s) => (s -> (n, [(e, s)])) -> s -> (Vertex, LabGraph n e)
unfoldG f r = (r', res)
    where ([r'], res) = unfoldGMany f [r]

unfoldGMany :: (Ord s) => (s -> (n, [(e, s)])) -> [s] -> ([Vertex], LabGraph n e)
unfoldGMany f roots = runST ( unfoldGManyST f roots )

foldG :: (Eq r) => r -> (Vertex -> [(e, r)] -> r) -> Graph e -> Vertex -> r
foldG i f g v = foldGAll i f g ! v

foldGAll :: (Eq r) => r -> (Vertex -> [(e, r)] -> r) -> Graph e -> Table r
foldGAll bot f gr = finalTbl
    where finalTbl = fixedPoint updateTbl initialTbl
          initialTbl = listArray bnds (replicate (rangeSize bnds) bot)
 
          fixedPoint f x = fp x
              where fp z = if z == z' then z else fp z'
                        where z' = f z
          updateTbl tbl = listArray bnds $ map recompute $ indices gr
              where recompute v = f v [(b, tbl!k) | (b, k) <- gr!v]
          bnds = bounds gr

-- | Build a graph from a list of edges.
buildG :: Bounds -> [Edge e] -> Graph e
buildG bounds0 edges0 = accumArray (flip (:)) [] bounds0 [(v, (l,w)) | (v,l,w) <- edges0]
 
-- | The graph obtained by reversing all edges.
transposeG  :: Graph e -> Graph e
transposeG g = buildG (bounds g) (reverseE g)
 
reverseE    :: Graph e -> [Edge e]
reverseE g   = [ (w, l, v) | (v, l, w) <- edges g ]


showGraphViz (LabGraph gr lab)
    = "digraph name {\n"
      ++ "rankdir=LR;\n"
      ++ (concatMap showNode $ indices gr)
      ++ (concatMap showEdge $ edges gr)
      ++ "}\n"
    where showEdge (from, t, to) = show from ++ " -> " ++ show to ++
				   " [label = \"" ++ show t ++ "\"];\n"
          showNode v = show v ++ " [label = " ++ (show $ lab v) ++ "];\n"
 
edges :: Graph e -> [Edge e]
edges g = [ (v, l, w) | v <- indices g, (l, w) <- g!v ]

unfoldGManyST :: (Ord a) => (a -> (c, [(b, a)]))
             -> [a] -> ST s ([Vertex], LabGraph c b)
unfoldGManyST gen seeds =
     do mtab <- newSTRef (Map.empty)
        allNodes <- newSTRef []
        vertexRef <- newSTRef firstId
        let allocVertex = 
                do vertex <- readSTRef vertexRef
                   writeSTRef vertexRef (vertex + 1)
                   return vertex
        let cyc src =
             do probe <- memTabFind mtab src
                case probe of
                   Just result -> return result
                   Nothing -> do
                     v <- allocVertex
                     memTabBind src v mtab 
                     let (lab, deps) = gen src
                     ws <- mapM (cyc . snd) deps
                     let res = (v, lab, [(fst d, w) | d <- deps | w <- ws])
                     modifySTRef allNodes (res:)
                     return v
        mapM_ cyc seeds
        list <- readSTRef allNodes
        seedsResult <- (return . map fromJust) =<< mapM (memTabFind mtab) seeds
        lastId <- readSTRef vertexRef
        let cycamore = array (firstId, lastId-1) [(i, k) | (i, a, k) <- list]
        let labels = array (firstId, lastId-1) [(i, a) | (i, a, k) <- list]
        return (seedsResult, LabGraph cycamore (labels !))
   where firstId = 0::Vertex
         memTabFind mt key = return . Map.lookup key =<< readSTRef mt
         memTabBind key val mt = modifySTRef mt (Map.insert key val)