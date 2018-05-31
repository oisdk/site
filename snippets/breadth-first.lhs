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
  f (Node x xs) qs = (x:z) : foldr f zs xs where
    (z,zs) = case qs of
      [] -> ([],[])
      (y:ys) -> (y,ys)
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
    liftA2 (\y -> (y :<) . rt) (c t) (rbld (foldr f [] ts))
  where
    rt = evalState (fill ts)
    f (x :< xs) qs = cons (fill xs) (c x) z : foldr f zs xs where
      (z,zs) = case qs of
        [] -> (pure (pure []), [])
        (y:ys) -> (y,ys)
    rbld = foldr (liftA2 evalState) (pure [])
    fill = traverse (const (state (\(x:xs) -> (x, xs))))
    cons ys = liftA2 (\x -> liftA2 ((:) . (:<) x) ys)
\end{code}
