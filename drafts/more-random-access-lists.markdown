---
title: More Random Access Lists
series: Random Access Lists
tags: Haskell, Agda
---

Many data structures are derived from numeric representations: lists, famously,
are deeply related the natural numbers.
More efficient data structures, then, often come from more efficient numeric
representations.
Today I'm going to look again at binary random-access lists, and the zeroless
binary numbers.

# Zeroless Binary

I implemented these numbers
[previously](2019-11-02-how-to-binary-random-access-list.html#6377), so I won't
describe them fully again, but basically they are the *simplest* way to
represent the natural numbers using a list of bits.
Traditional binary has trailing zeroes: the numbers `010` and `0010` both
represent 2, which can cause problems in practice (especially if you want to
verify things).

Zeroless binary doesn't have `0` bits at all: it only has `1`s and `2`s.
Since I did the conversion functions in Agda last time, I'll write them here in
Haskell:

```haskell
toBits :: Natural -> [Bool]
toBits = unfoldr f
  where
    f 0 = Nothing
    f n = Just (even n, (n - 1) `div` 2)
    
fromBits :: [Bool] -> Natural
fromBits = foldr f 0
  where
    f False xs = 1 + xs * 2
    f True  xs = 2 + xs * 2
```

We can work directly on the bits here (from the input number), which makes
things a little faster.
We still of course have increment:

```haskell
inc :: [Bool] -> [Bool]
inc [] = [False]
inc (False:xs) = True  : xs
inc (True :xs) = False : inc xs
```

# Containers, Tries, and Memoization

One of the most amazing tricks Haskell can do is pure memoization: using
laziness, we can build a (possibly infinite) data structure representing the
*trie* of some argument type, fill it with the result of evaluating some
expensive function, and the *lookup* in that structures will be the memoized
function.
(Call-by-need) Laziness means that any field in the data structure won't be
evaluated twice, and it also means that we won't evaluate any fields we don't
use.

Here's an example with just the booleans:

```haskell
data BoolTrie a
  = BoolTrie
  { onFalse :: a
  , onTrue  :: a
  }
  
memoize :: (Bool -> a) -> Bool -> a
memoize f = lookup trie
  where
    trie =
      BoolTrie { onFalse = f False
               , onTrue  = f True
               }

    lookup trie False = onFalse trie
    lookup trie True  = onTrue  trie
```

And you can 
