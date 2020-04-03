---
title: Rotations
tags: Haskell
---

This is just some cool-looking stuff I figure out when I was trying to figure out zipper-like algorithms. When I do get around to doing a deep dive on zippers (especially comonadic zippers) I'll probably be able to write a full post on some of the underlying theory (with maybe some more efficient implementations).

```haskell
{-# LANGUAGE FlexibleContexts #-}

module Rotations where

import Control.Monad.Tardis
import Control.Applicative ((<**>))

-- | >>> rotations "abcd"
-- ["abcd","bcda","cdab","dabc"]
rotations :: [a] -> [[a]]
rotations = flip evalTardis (id,id) . traverse f
  where
    f x = do
      xs <- pure [] <**> getPast <**> getFuture
      modifyBackwards ((:) x .)
      modifyForwards  (. (:) x)
      pure xs
```
