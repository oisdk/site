---
title: Choose a random item from a list in one pass
---

Adapted from [here](https://blog.plover.com/prog/weighted-reservoir-sampling.html).

\begin{code}
{-# LANGUAGE BangPatterns #-}

module Choose where

import System.Random
import GHC.Base (oneShot)

choose :: (Foldable f, RandomGen g) =>  f a -> g -> (Maybe a, g)
choose xs = foldr f (const (,)) xs (0 :: Integer) Nothing
  where
    f x a = oneShot (\ !c m g -> case m of 
      Nothing -> a 1 (Just x) g
      Just y -> case randomR (0,c) g of
        (0,g') -> a (c+1) (Just x) g'
        (_,g') -> a (c+1) (Just y) g')
    {-# INLINE f #-}
\end{code}
