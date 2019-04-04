---
title: Unfoldl
---

\begin{code}
{-# LANGUAGE LambdaCase #-}

module Unfoldl where

import GHC.Base (build)
import Data.Tuple (swap)

unfoldl :: (b -> Maybe (a, b)) -> b -> [a]
unfoldl f b =
    build
        (\c n ->
              let r a = maybe a (uncurry (r . (`c` a))) . f
              in r n b)

-- | >>> toDigs 10 123
-- [1,2,3]
toDigs :: (Integral a, Num a) => a -> a -> [a]
toDigs base =
  unfoldl (\case
    0 -> Nothing
    n -> Just (swap (n `quotRem` base)))
\end{code}
