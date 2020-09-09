---
title: Revealing Algorithms With Scott Encoding
tags: Haskell
---

There are some techniques for writing functional code that have very bad
reputations: point-free code, for instance, or church encoding.
Both of these techniques have their benefits, but they can also result in overly
complex, hard-to-understand functions.
As a result people can push back against them.

Aside from being useful techniques for actual code (church encoding can often
yield serious speedups), I like to use them as kind of manual optimisation
passes. 
If I'm trying to figure out a tricky algorithm or something, often if I
aggressively church-encode every data type it can reveal redundancies or
opportunities for optimisation.
It also forces you to look at an algorithm inside-out, in a way, which can yield
new insights to the problem. 

Today, we're going to aggressively church-encode (well, actually it will be
Scott encoding) quick sort, and see what insights that gives us.

To start we'll need a (bad) implementation of quick sort.

```haskell
qsort :: [a] -> [a]
qsort [] = []
qsort (x:xs) = qsort lte ++ [x] ++ qsort gt
  where
    (lte,gt) = partition (<=x) xs
```

So, first things first, this algorithm is quadratic.
The fact that we're using `++` rather than difference lists is the culprit for
that.
The following is the corrected version:

```haskell
qsort :: [a] -> [a]
qsort xs = go xs []
  where
    go []     ys = ys
    go (x:xs) ys = go lte (x : go gt ys)
      where
        (lte,gt) = partition (<=x) xs
```

This still is a pretty bad implementation of quick sort: it's not in place, and
chooses an absolutely awful pivot element (the first element in the list).
Quick sort's worst case complexity is $O(n^2)$, and our choice of pivot will
ensure that we run into that worst case quite frequently.

But I am not going to explain exactly *why* that choice of pivot is so bad for
the time being.
Instead, we're going to try and church encode this algorithm as much as we can,
removing all explicit lists from view.
