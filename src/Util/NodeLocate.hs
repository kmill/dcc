{-# LANGUAGE RankNTypes, GADTs, ScopedTypeVariables, FlexibleInstances #-}

-- | This module provides functions to be able to have pointers to
-- nodes inside of basic blocks.

module Util.NodeLocate where

import Compiler.Hoopl
import qualified IR as I
import Assembly

data NodePtr = NodePtr Label Int
               deriving (Eq, Ord)

nodeLabel :: NodePtr -> Label
nodeLabel (NodePtr l _) = l
                        
instance Show NodePtr where
    show (NodePtr l i) = show l ++ "." ++ show i

makeStartPtr :: Label -> NodePtr
makeStartPtr l = NodePtr l 0

nextNodePtr :: NodePtr -> NodePtr
nextNodePtr (NodePtr l i) = NodePtr l (i + 1)

prevNodePtr :: NodePtr -> NodePtr
prevNodePtr (NodePtr l i) = NodePtr l (i + 1)

data PNode n e x where
    PNode :: NodePtr -> n e x -> PNode n e x

instance NonLocal n => NonLocal (PNode n) where
    entryLabel (PNode _ n) = entryLabel n
    successors (PNode _ n) = successors n

instance Show (PNode Asm e x) where
    show (PNode ptr node) = show ptr ++ ": " ++ show node
instance Show (PNode I.MidIRInst e x) where
    show (PNode ptr node) = show ptr ++ ": " ++ show node

toPGraph :: NonLocal n => Graph n C C -> Graph (PNode n) C C
toPGraph g = g'
    where GMany _ body _ = g
          g' = foldl (|*><*|) emptyClosedGraph bodies
          bodies = map toP' (mapElems body)
          toP' :: forall n. NonLocal n => Block n C C -> Graph (PNode n) C C
          toP' block = let (me, inner, mx) = blockToNodeList block
                           e :: n C O
                           x :: n O C
                           e = case me of
                                 JustC e' -> e'
                           x = case mx of
                                 JustC x' -> x'
                           l = entryLabel block
                           innerptrs = map (\i -> PNode $ NodePtr l i) [1..]
                           lastptr = NodePtr l (1 + length inner)
                       in mkFirst (PNode (NodePtr l 0) e)
                              <*> mkMiddles (map (uncurry ($)) (zip innerptrs inner))
                              <*> mkLast (PNode lastptr x)