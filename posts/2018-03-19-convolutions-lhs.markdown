---
title: Convolutions
tags: Haskell
---

Convolutions of a list give a different traversal order than what you would traditionally expect. Adapted from [here](https://byorgey.wordpress.com/2008/04/22/list-convolutions/).

```haskell
-- | >>> mapM_ print ([1..5] <.> [1..5])
-- [(1,1)]
-- [(1,2),(2,1)]
-- [(1,3),(2,2),(3,1)]
-- [(1,4),(2,3),(3,2),(4,1)]
-- [(1,5),(2,4),(3,3),(4,2),(5,1)]
-- [(2,5),(3,4),(4,3),(5,2)]
-- [(3,5),(4,4),(5,3)]
-- [(4,5),(5,4)]
-- [(5,5)]
(<.>) :: [a] -> [b] -> [[(a,b)]]
xs <.> ys = foldr f [] xs where
  f x = foldr g id ys . ([] :) where
    g y k ~(z :~ zs) = ((x,y) : z) : k zs

unconsMon :: Monoid m => [m] -> (m, [m])
unconsMon (x:xs) = (x, xs)
unconsMon []     = (mempty, [])

pattern (:~) :: Monoid m => m -> [m] -> [m]
pattern (:~) x xs <- (unconsMon -> (x, xs))
```
