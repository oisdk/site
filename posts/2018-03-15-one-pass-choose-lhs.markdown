---
title: Choose a random item from a list in one pass
tags: Haskell
---

Adapted from [here](https://blog.plover.com/prog/weighted-reservoir-sampling.html).

```haskell
import System.Random

choose :: (Foldable f, RandomGen g) =>  f a -> g -> (a, g)
choose xs g = h (foldl f (0 :: Integer, error "choose: empty list", g) xs)
  where
    h (_,x,g) = (x,g)
    f (c,y,g) x = case randomR (0,c) g of
        (0,g') -> (c+1,x,g')
        (_,g') -> (c+1,y,g')
```
