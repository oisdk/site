---
title: Convolutions
---

Convolutions of a list give a different traversal order than what you would traditionally expect. Adapted from [here](https://byorgey.wordpress.com/2008/04/22/list-convolutions/).

\begin{code}
module Convolve where

-- | >>> [1,2,3] <.> [4,5,6]
-- [[(1,4)],[(1,5),(2,4)],[(1,6),(2,5),(3,4)],[(2,6),(3,5)],[(3,6)]]
(<.>) :: [a] -> [b] -> [[(a,b)]]
_ <.> [] = []
xs <.> (yh:ys) = foldr f [] xs
  where
    f x zs = [(x,yh)] : foldr (g x) id ys zs
    g x y a (z:zs) = ((x, y) : z) : a zs
    g x y a [] = [(x, y)] : a []
\end{code}
