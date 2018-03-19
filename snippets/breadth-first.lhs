---
title: Breadth-First Rose Tree Traversals
---

These use implicit queues to efficiently perform breadth-first operations on rose trees.

\begin{code}
module BreadthFirst where

import Data.Tree
\end{code}

The most basic is simply converting to a list breadth-first:

\begin{code}
breadthFirst :: Tree a -> [a]
breadthFirst (Node x xs) = x : breadthFirstForest xs

breadthFirstForest :: Forest a -> [a]
breadthFirstForest ts = foldr f b ts []
  where
    f (Node x xs) fw bw = x : fw (xs : bw)

    b [] = []
    b qs = foldl (foldr f) b qs []
\end{code}

Then, we can delimit between levels of the tree:

\begin{code}
levels :: Tree a -> [[a]]
levels (Node x xs) = [x] : levelsForest xs

levelsForest :: Forest a -> [[a]]
levelsForest ts = foldl f b ts [] []
  where
    f k (Node x xs) ls qs = k (x : ls) (xs : qs)

    b _ [] = []
    b k qs = k : foldl (foldl f) b qs [] []
\end{code}

Finally, we can build a tree back up again, monadically.

\begin{code}
unfoldForestM_BF :: Monad m => (b -> m (a, [b])) -> [b] -> m (Forest a)
unfoldForestM_BF = unfoldForestMWith_BF concat

unfoldTreeM_BF :: Monad m => (b -> m (a, [b])) -> b -> m (Tree a)
unfoldTreeM_BF f b = unfoldForestMWith_BF (head . head) f [b]

unfoldForestMWith_BF :: Monad m => ([Forest a] -> c) -> (b -> m (a, [b])) -> [b] -> m c
unfoldForestMWith_BF r f ts = b [ts] (\ls -> r . ls)
  where
    b [] k = pure (k id [])
    b qs k = foldl g b qs [] (\ls -> k id . ls)

    g a xs qs k = foldr t (\ls ys -> a ys (k . run ls)) xs [] qs

    t a fw xs bw = f a >>= \(x,cs) -> fw (x:xs) (cs:bw)

    run x xs = uncurry (:) . foldl go ((,) [] . xs) x
      where
        go ys y (z:zs) = (Node y z : ys', zs')
          where
            (ys',zs') = ys zs
\end{code}
