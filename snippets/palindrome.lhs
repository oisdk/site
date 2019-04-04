---
title: Palindrome Test
---

Test if a list is a palindrome, in an unnecessarily complicated way.

\begin{code}
module Palindrome where

isPal :: Eq a => [a] -> Bool
isPal xs = go xs xs (const True)  where
  go (y:ys) (_:_:zs) k = go ys zs (\(z:zzs) -> y == z && k zzs)
  go (_:ys) [_] k = k ys
  go ys [] k = k ys
\end{code}
