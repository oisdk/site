---
title: Partitions of a List
---

\begin{code}
module Partitions where

import Data.Foldable

-- | >>> partitions "abc"
-- [["abc"],["a","bc"],["ab","c"],["ac","b"],["a","b","c"]]
partitions :: [a] -> [[[a]]]
partitions = foldrM f [] where
  f x xs = go id xs where
    go k [] = [[x] : k []]
    go k (y:ys) = ((x:y) : k ys) : go (k . (:) y) ys
\end{code}
