---
title: Breadth-First Rose Tree Traversals
---

These use implicit queues to efficiently perform breadth-first operations on rose trees.

\begin{code}
module BreadthFirst where

import Control.Comonad.Cofree
import Data.Tree
import Control.Applicative
import Control.Monad.State
\end{code}

The most basic is simply converting to a list breadth-first:

\begin{code}
breadthFirstTree :: Tree a -> [a]
breadthFirstTree tr = f tr b []
  where
    f (Node x xs) fw bw = x : fw (xs : bw)

    b [] = []
    b qs = foldl (foldr f) b qs []
\end{code}

Then, we can delimit between levels of the tree:

\begin{code}
levels :: Tree a -> [[a]]
levels tr = f tr [] where
  f (Node x xs) (y:ys) = (x:y) : foldr f ys xs
  f (Node x xs) []     = [x]   : foldr f [] xs
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

To generalize some more, we can write a traversal (in the lensy sense) of the cofree comonad:

\begin{code}
breadthFirst
    :: (Applicative f, Traversable t)
    => (a -> f b) -> Cofree t a -> f (Cofree t b)
breadthFirst c (t :< ts) =
    liftA2 evalState (map2 (:<) (c t) (fill ts)) chld
  where
    chld = foldr (liftA2 evalState) (pure []) (foldr f [] ts)
    fill = traverse (const (state (\(x:xs) -> (x,xs))))

    f (x:<xs) (q:qs) = app2 (\y ys zs -> (y:<ys) : zs) (c x) (fill xs) q
                     : foldr f qs xs
    f (x:<xs) []     = map2 (\y ys    -> (y:<ys) : []) (c x) (fill xs)
                     : foldr f [] xs

    map2 = flip . (fmap   .) . flip . (fmap   .)
    app2 = flip . (liftA2 .) . flip . (liftA2 .)
\end{code}
