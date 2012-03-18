{-# LANGUAGE ParallelListComp #-}

-- | from
-- http://www.haskell.org/haskellwiki/The_Monad.Reader/Issue5/Practical_Graph_Handling

module Data.Graphs where

import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Text.Regex
import Debug.Trace

type Vertex = Int

-- | A pointed directed multigraph.  That is, there is a specified
-- "start vertex" to the graph.
data Ord e => Graph v e
    = Graph (Map.Map Vertex (v, Map.Map e Vertex)) Vertex
      deriving Show
      
startVertex :: Ord e => Graph v e -> Vertex
startVertex (Graph m st) = st

vertices :: Ord e => Graph v e -> [Vertex]
vertices (Graph m st) = Map.keys m

labels :: Ord e => Graph v e -> [(Vertex,v)]
labels (Graph m st) = Map.assocs (Map.map (\(v,e)->v) m)

(!!!) :: Ord e => Graph v e -> Vertex -> v
(Graph m st) !!! i = fst $ fromJust $ Map.lookup i m

edges :: Ord e => Graph v e -> [(Vertex, e, Vertex)]
edges (Graph m st) = concatMap (\(i,(_,es)) -> [(i,l,e) | (l,e) <- Map.assocs es])
                     (Map.assocs m)

hasEdge :: Ord e => Graph v e -> Vertex -> e -> Bool
hasEdge (Graph m _) v e = e `Map.member` (snd $ fromJust $ Map.lookup v m)

withStartVertex :: Vertex -> [(e, Vertex)] -> [(Vertex,e,Vertex)]
withStartVertex v es = map (\(l,end) -> (v,l,end)) es

adjEdges :: Ord e => Graph v e -> Vertex -> [(e,Vertex)]
adjEdges (Graph m st) i = Map.assocs $ snd $ fromJust $ Map.lookup i m

adjVertices :: Ord e => Graph v e -> Vertex -> [Vertex]
adjVertices (Graph m st) i = map snd $ Map.assocs $ snd $ fromJust $ Map.lookup i m

-- | The vertices which lead to a particular vertex.
preVertices :: Ord e => Graph v e -> Vertex -> [Vertex]
preVertices g v = [vert | vert <- vertices g, v `elem` (adjVertices g vert)]

createGraph :: Ord e => [(Vertex, v)] -> [(Vertex, e, Vertex)] -> Vertex -> Graph v e
createGraph verts edges st
    = Graph (Map.fromList $ map attachEdges verts) st
      where attachEdges (i, v)
                = (i, (v
                      , Map.fromList [(l, end) | (st, l, end) <- edges, i == st]))

replaceVertices :: (Show v, Show e, Ord e) => Graph v e -- | ^ initial graph
                -> [Vertex] -- | ^ vertices to replace
                -> [(Vertex, v)] -- | ^ vertices to replace them with
                -> [(Vertex, e, Vertex)] -- | ^ edges to insert
                -> Graph v e -- | ^ result of replacement
replaceVertices g vs newvs newedges
    = let newvertices = (filter (\(i,_) -> i `notElem` vs) (labels g)) ++ newvs
          edges' = (filter (\(s,_,_) -> s `notElem` vs) (edges g)) ++ newedges
      in createGraph newvertices edges' (startVertex g)

testReplVerts :: IO ()
testReplVerts
    = let g = createGraph [(1,1), (2,2), (3,3), (4,4)]
              [(1,True,2), (2,True,3), (3,True,4), (2,False,3)]
              1
      in do putStrLn $ graphToGraphViz g "" ""
            let g' = replaceVertices g [2,3] [(2,10)] [(2,True,4)]
            putStrLn $ graphToGraphViz g' "" ""

---
--- Graph algorithms!
---

-- | Walk through the graph and return the subgraph reachable by the
-- start vertex.
cullGraph :: Ord e => Graph v e -> Graph v e
cullGraph g@(Graph m st) = cullGraph' [] [st]
    where cullGraph' visited visit
              = case unvisitedNeighbors of
                  [] -> Graph
                         (Map.filterWithKey (\k v -> k `elem` visited') m)
                         st
                  next -> cullGraph' (visited ++ visit) next
              where visited' = visited ++ visit
                    unvisitedNeighbors
                        = filter (`notElem` visited')
                          (concatMap (adjVertices g) visit)

data GraphPattern v e a = GraphPattern { runRewrite :: Maybe a }

instance Monad (GraphPattern v e) where
  ma >>= f = case runRewrite ma of
               Just a -> f a
               Nothing -> GraphPattern Nothing
  return x = GraphPattern (Just x)
instance MonadPlus (GraphPattern v e) where
  mzero = GraphPattern Nothing
  ma `mplus` mb = case runRewrite ma of
                    Just a -> ma
                    Nothing -> mb

type RewriteRule v e = Graph v e -> Vertex -> GraphPattern v e ([Vertex], [(Vertex,v)], [(Vertex,e,Vertex)])

gReplace :: [Vertex] -- | ^ vertices to replace
         -> [(Vertex, v)] -- | ^ vertices to replace them with
         -> [(Vertex, e, Vertex)] -- | ^ edges to insert
         -> GraphPattern v e ([Vertex], [(Vertex,v)], [(Vertex,e,Vertex)])
gReplace vs newvs edges = return (vs, newvs, edges)

-- | Takes a graph and a rewrite rule, and walks along the graph,
-- possibly rewriting stuff.  TODO make sure this is a reasonable way
-- to do this!  As of now, doesn't check to see if we reach a fixed
-- point, for instance (which can be fixed by essentially running the
-- algorithm a number of times).
rewriteGraph :: (Show v, Show e, Ord e) => Graph v e -> RewriteRule v e -> Graph v e
rewriteGraph g rule = rewriteGraph' g [] [startVertex g]
    where rewriteGraph' g visited toVisit
              = case toVisit of
                  [] -> g
                  v:vs ->
                    case v `elem` (vertices g) of
                      False -> rewriteGraph' g visited vs
                      True ->
                          case runRewrite (rule g v) of
                            Nothing -> rewriteGraph' g (visited ++ [v])
                                       (vs ++ [n | n <- adjVertices g v,
                                               n `notElem` (visited ++ toVisit ++ [v])])
                            Just (oldvs, newvs, edges)
                                -> rewriteGraph'
                                   (cullGraph $ replaceVertices g oldvs newvs edges)
                                   visited ((map fst newvs) ++ vs)

---
--- Graph display!
---

graphToGraphViz' :: (Show v, Show e, Ord e) => Graph v e -> String -> String
graphToGraphViz' g namePrefix
    = concatMap showVertex (vertices g)
      where showVertex i
                = namePrefix ++ show i
                   ++ " [ shape=box, label="
                   ++ (leftAlign $ show $ show (g !!! i) ++ "\n") ++ "];\n"
                   ++ (concatMap (showEdge i) (adjEdges g i))
            showEdge start (edge,i)
                = namePrefix ++ show start
                  ++ " -> " ++ namePrefix ++ show i
                  ++ " [label=" ++ show edge ++ "];\n"
            -- | turns \n into \l so graphviz left-aligns
            leftAlign t = subRegex (mkRegex "\\\\n") t "\\l"

graphToGraphViz :: (Show v, Show e, Ord e) => Graph v e -> String -> String -> String
graphToGraphViz g namePrefix graphPrefix
    = "digraph {\n"
      ++ graphPrefix ++ "\n"
      ++ graphToGraphViz' g namePrefix
      ++ "}\n"

graphToGraphVizSubgraph :: (Show v, Show e, Ord e) => Graph v e -> String -> String -> String
graphToGraphVizSubgraph g namePrefix graphPrefix
    = "subgraph {\n"
      ++ graphPrefix ++ "\n"
      ++ graphToGraphViz' g namePrefix
      ++ "}\n"

-- type Vertex = Int
-- type Table a = Array Vertex a
-- type Graph e = Table [(e, Vertex)]
-- type Bounds  = (Vertex, Vertex)
-- type Edge e = (Vertex, e, Vertex)

-- type Labeling a = Vertex -> a
-- data LabGraph n e = LabGraph (Graph e) (Labeling n)
 
-- vertices (LabGraph gr _) = indices gr
 
-- labels (LabGraph gr l) = map l (indices gr)


-- unfoldG :: (Ord s) => (s -> (n, [(e, s)])) -> s -> (Vertex, LabGraph n e)
-- unfoldG f r = (r', res)
--     where ([r'], res) = unfoldGMany f [r]

-- unfoldGMany :: (Ord s) => (s -> (n, [(e, s)])) -> [s] -> ([Vertex], LabGraph n e)
-- unfoldGMany f roots = runST ( unfoldGManyST f roots )

-- foldG :: (Eq r) => r -> (Vertex -> [(e, r)] -> r) -> Graph e -> Vertex -> r
-- foldG i f g v = foldGAll i f g ! v

-- foldGAll :: (Eq r) => r -> (Vertex -> [(e, r)] -> r) -> Graph e -> Table r
-- foldGAll bot f gr = finalTbl
--     where finalTbl = fixedPoint updateTbl initialTbl
--           initialTbl = listArray bnds (replicate (rangeSize bnds) bot)
 
--           fixedPoint f x = fp x
--               where fp z = if z == z' then z else fp z'
--                         where z' = f z
--           updateTbl tbl = listArray bnds $ map recompute $ indices gr
--               where recompute v = f v [(b, tbl!k) | (b, k) <- gr!v]
--           bnds = bounds gr

-- -- | Build a graph from a list of edges.
-- buildG :: Bounds -> [Edge e] -> Graph e
-- buildG bounds0 edges0 = accumArray (flip (:)) [] bounds0 [(v, (l,w)) | (v,l,w) <- edges0]
 
-- -- | The graph obtained by reversing all edges.
-- transposeG  :: Graph e -> Graph e
-- transposeG g = buildG (bounds g) (reverseE g)
 
-- reverseE    :: Graph e -> [Edge e]
-- reverseE g   = [ (w, l, v) | (v, l, w) <- edges g ]


-- showGraphViz (LabGraph gr lab)
--     = "digraph name {\n"
--       ++ "rankdir=LR;\n"
--       ++ (concatMap showNode $ indices gr)
--       ++ (concatMap showEdge $ edges gr)
--       ++ "}\n"
--     where showEdge (from, t, to) = show from ++ " -> " ++ show to ++
-- 				   " [label = \"" ++ show t ++ "\"];\n"
--           showNode v = show v ++ " [label = " ++ (show $ lab v) ++ "];\n"
          
-- instance (Show a, Show b) => Show (LabGraph a b) where
--     show = showGraphViz
          
-- edges :: Graph e -> [Edge e]
-- edges g = [ (v, l, w) | v <- indices g, (l, w) <- g!v ]

-- unfoldGManyST :: (Ord a) => (a -> (c, [(b, a)]))
--              -> [a] -> ST s ([Vertex], LabGraph c b)
-- unfoldGManyST gen seeds =
--      do mtab <- newSTRef (Map.empty)
--         allNodes <- newSTRef []
--         vertexRef <- newSTRef firstId
--         let allocVertex = 
--                 do vertex <- readSTRef vertexRef
--                    writeSTRef vertexRef (vertex + 1)
--                    return vertex
--         let cyc src =
--              do probe <- memTabFind mtab src
--                 case probe of
--                    Just result -> return result
--                    Nothing -> do
--                      v <- allocVertex
--                      memTabBind src v mtab 
--                      let (lab, deps) = gen src
--                      ws <- mapM (cyc . snd) deps
--                      let res = (v, lab, [(fst d, w) | d <- deps | w <- ws])
--                      modifySTRef allNodes (res:)
--                      return v
--         mapM_ cyc seeds
--         list <- readSTRef allNodes
--         seedsResult <- (return . map fromJust) =<< mapM (memTabFind mtab) seeds
--         lastId <- readSTRef vertexRef
--         let cycamore = array (firstId, lastId-1) [(i, k) | (i, a, k) <- list]
--         let labels = array (firstId, lastId-1) [(i, a) | (i, a, k) <- list]
--         return (seedsResult, LabGraph cycamore (labels !))
--    where firstId = 0::Vertex
--          memTabFind mt key = return . Map.lookup key =<< readSTRef mt
--          memTabBind key val mt = modifySTRef mt (Map.insert key val)