{-# LANGUAGE ParallelListComp #-}

-- | We represent graphs as a set of vertices (which is a subset of
-- the integers), a set of labeled edges (where each label is unique),
-- and a map from vertices to labels.  This module also has various
-- graph algorithms.

module Data.Graphs where

import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import Text.Regex
--import Debug.Trace
import qualified Data.Traversable as Trav

type Vertex = Int

-- | A pointed directed labeled multigraph.  That is, there is a
-- specified "start vertex" to the graph, and each of the vertices
-- have a label.
data Ord e => Graph v e
    = Graph (Map.Map Vertex (v, Map.Map e Vertex)) Vertex
      deriving Show

-- | Gets the distinguished vertex from the graph.
startVertex :: Ord e => Graph v e -> Vertex
startVertex (Graph m st) = st

-- | Gets a list of the graph's vertices.
vertices :: Ord e => Graph v e -> [Vertex]
vertices (Graph m st) = Map.keys m

-- | Gets a list of the vertex/label pairs for the graph.
labels :: Ord e => Graph v e -> [(Vertex,v)]
labels (Graph m st) = Map.assocs (Map.map (\(v,e)->v) m)

-- | Gets the label in a graph
(!!!) :: Ord e => Graph v e -> Vertex -> v
(Graph m st) !!! i = fst $ fromJust $ Map.lookup i m

edges :: Ord e => Graph v e -> [(Vertex, e, Vertex)]
edges (Graph m st) = concatMap (\(i,(_,es)) -> [(i,l,e) | (l,e) <- Map.assocs es])
                     (Map.assocs m)

hasEdge :: Ord e => Graph v e -> Vertex -> e -> Bool
hasEdge (Graph m _) v e = e `Map.member` (snd $ fromJust $ Map.lookup v m)

hasEdgeTo :: Ord e => Graph v e -> Vertex -> e -> Vertex -> Bool
hasEdgeTo (Graph m _) v e v'
  = fromMaybe False $ do
      v'' <- Map.lookup e (snd $ fromJust $ Map.lookup v m)
      return $ v' == v''

withStartVertex :: Vertex -> [(e, Vertex)] -> [(Vertex,e,Vertex)]
withStartVertex v es = map (\(l,end) -> (v,l,end)) es

adjEdges :: Ord e => Graph v e -> Vertex -> [(e,Vertex)]
adjEdges (Graph m st) i = Map.assocs $ snd $ fromJust $ Map.lookup i m

adjVertices :: Ord e => Graph v e -> Vertex -> [Vertex]
adjVertices (Graph m st) i = map snd $ Map.assocs $ snd $ fromJust $ Map.lookup i m

-- | The vertices which lead to a particular vertex.
preVertices :: Ord e => Graph v e -> Vertex -> [Vertex]
preVertices g v = [vert | vert <- vertices g, v `elem` (adjVertices g vert)]

-- | Gets a Vertex number which has been unused by the graph.
freshVertex :: Ord e => Graph v e -> Vertex
freshVertex g = head (filter (`notElem` (vertices g)) [0..])

createGraph :: Ord e => [(Vertex, v)] -> [(Vertex, e, Vertex)] -> Vertex -> Graph v e
createGraph verts edges st
    = Graph (Map.fromList $ map attachEdges verts) st
      where attachEdges (i, v)
                = (i, (v
                      , Map.fromList [(l, end) | (st, l, end) <- edges, i == st]))

replaceVertices :: Ord e => Graph v e -- | ^ initial graph
                -> [Vertex] -- | ^ vertices to replace
                -> [(Vertex, v)] -- | ^ vertices to replace them with
                -> [(Vertex, e, Vertex)] -- | ^ edges to insert
                -> Graph v e -- | ^ result of replacement
replaceVertices g vs newvs newedges
    = let newvertices = (filter (\(i,_) -> i `notElem` vs) (labels g)) ++ newvs
          edges' = (filter (\(s,_,_) -> s `notElem` vs) (edges g)) ++ newedges
      in createGraph newvertices edges' (startVertex g)

graphWithNewStart :: Ord e => Graph v e -> Vertex -> v -> [(e,Vertex)] -> Graph v e
graphWithNewStart g newst vert edges
    = let Graph m _
              = replaceVertices g [] [(newst, vert)] (withStartVertex newst edges)
      in Graph m newst

---
--- Maps
---

mapG :: Ord e => (v -> w) -> Graph v e -> Graph w e
mapG f (Graph m st) = Graph (Map.map (\(v, es) -> (f v, es)) m) st

mapGWithKey :: Ord e => (Vertex -> v -> w) -> Graph v e -> Graph w e
mapGWithKey f (Graph m st) = Graph (Map.mapWithKey (\k (v, es) -> (f k v, es)) m) st

mapGM :: (Monad m, Ord e) => (v -> m w) -> Graph v e -> m (Graph w e)
mapGM f (Graph m st) =
    do m' <- flip Trav.mapM m (\(v, es) ->
                               do v' <- f v
                                  return (v', es))
       return $ Graph m' st

---
--- Graph iteration stuff
---

iterG :: Ord e => (Graph v e -> Vertex -> r -> Maybe ([Vertex], r)) -> r -> Graph v e -> r
iterG f i g = iterG' i [] [startVertex g]
    where iterG' r visited tovisit
              = case tovisit of
                  [] -> r
                  v:vs ->
                      case f g v r of
                        Nothing ->
                            iterG' r (v:visited)
                               ((filter (`notElem` (visited++tovisit))
                                            (adjVertices g v))
                                ++ vs)
                        Just (nextvs, r') ->
                            iterG' r' visited ([v] ++ nextvs ++ vs)

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

(|||) :: RewriteRule v e -> RewriteRule v e -> RewriteRule v e
(r1 ||| r2) g v = (r1 g v) `mplus` (r2 g v)

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
rewriteGraph :: Ord e => Graph v e -> RewriteRule v e -> Graph v e
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
                                   (replaceVertices g oldvs newvs edges) -- maybe cull?
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
            leftAlign t = subRegex (mkRegex "([^\\\\])\\\\n") t "\\1\\l"

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

---
--- Test
---

testReplVerts :: IO ()
testReplVerts
    = let g = createGraph [(1,1), (2,2), (3,3), (4,4)]
              [(1,True,2), (2,True,3), (3,True,4), (2,False,3)]
              1
      in do putStrLn $ graphToGraphViz g "" ""
            let g' = replaceVertices g [2,3] [(2,10)] [(2,True,4)]
            putStrLn $ graphToGraphViz g' "" ""
