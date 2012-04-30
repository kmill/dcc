-- | This module provides functions to be able to have pointers to
-- nodes inside of basic blocks.

module Util.NodeLocate where

import Compiler.Hoopl

data NodePtr = NodePtr Label Int
               deriving (Eq, Ord)
                        
instance Show NodePtr where
    show (NodePtr l i) = show l ++ "." ++ show i

makeStartPtr :: Label -> NodePtr
makeStartPtr l = NodePtr l 0

nextNodePtr :: NodePtr -> NodePtr
nextNodePtr (NodePtr l i) = NodePtr l (i + 1)

prevNodePtr :: NodePtr -> NodePtr
prevNodePtr (NodePtr l i) = NodePtr l (i + 1)
