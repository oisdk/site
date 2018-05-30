---
title: Sorting Small Things in Haskell
tags: Haskell
series: Sorting
---

I was working on some performance-intensive stuff recently, and I ran into the issue of sorting very small amounts of values (think 3, 4, 5).

The standard way to do this is with [sorting networks](https://en.wikipedia.org/wiki/Sorting_network). The way I'll be using doesn't actually perform any parallelism (unfortunately), but it is a clean way to write the networks in Haskell without too much repetition.

[This](http://pages.ripco.net/~jgamble/nw.html) website will generate an optimal sorting network for your given size, and the output (for 3) looks like this:

```
[[1,2]]
[[0,2]]
[[0,1]]
```

Each pair of indices represents a "compare-and-swap" operation: so the first line means "compare the value at 1 to the value at 2: if it's bigger, swap them". For 5, the network looks like this:

```
[[0,1],[2,3]]
[[0,2],[1,3]]
[[1,2],[0,4]]
[[1,4]]
[[2,4]]
[[3,4]]
```

Pairs on the same line can be performed in parallel.

For our case, I'm going to be looking at sorting tuples, but the technique can easily be generalized to vectors, etc.

The first trick is to figure out how to do "swapping": we don't want mutation, so what we can do instead is swap the *reference* to some value, by shadowing its name. In other words:

```haskell
swap2 :: (a -> a -> Bool) -> a -> a -> (a, a)
swap2 lte x y | lte x y = (x, y)
              | otherwise = (y, x)

sort3 :: (a -> a -> Bool) -> (a,a,a) -> (a,a,a)
sort3 lte (_0,_1,_2)
    = case swap2 lte _1 _2 of
      (_1, _2) -> case swap2 lte _0 _2 of
        (_0, _2) -> case swap2 lte _0 _1 of
          (_0, _1) -> (_0, _1, _2)
```

The indentation is hard to read, though, and wrapping-and-unwrapping tuples makes me nervous about the performance (although it may be inlined). The next step is to *church-encode* the pairs returned:

```haskell
swap2 :: (a -> a -> Bool) -> a -> a -> (a -> a -> b) -> b
swap2 lte x y k
    | lte x y = k x y
    | otherwise = k y x

sort3 :: (a -> a -> Bool) -> (a,a,a) -> (a,a,a)
sort3 lte (_0,_1,_2)
    = swap2 lte _1 _2 $ \ _1 _2 ->
      swap2 lte _0 _2 $ \ _0 _2 ->
      swap2 lte _0 _1 $ \ _0 _1 ->
      (_0,_1,_2)
```

Then, to get this to compile down to efficient code, we can make judicious use of [`inline`{.haskell}](http://hackage.haskell.org/package/base-4.11.1.0/docs/GHC-Exts.html#v:inline) from GHC.Exts:

```haskell
import GHC.Exts (inline)

swap2 :: (a -> a -> Bool) -> a -> a -> (a -> a -> b) -> b
swap2 lte x y k
    | inline lte x y = inline k x y
    | otherwise = inline k y x
{-# INLINE swap2 #-}

sort3 :: (a -> a -> Bool) -> (a, a, a) -> (a, a, a)
sort3 lte (_0,_1,_2)
    = swap2 lte _1 _2 $ \ _1 _2 ->
      swap2 lte _0 _2 $ \ _0 _2 ->
      swap2 lte _0 _1 $ \ _0 _1 ->
      (_0,_1,_2)
{-# INLINE sort3 #-}
```

And to see if this really does make efficient code, let's look at the core (cleaned up):

```haskell
sort3
  = \ (lte :: a -> a -> Bool)
      (ds :: (a, a, a)) ->
      case ds of wild_X8 (_0, _1, _2) ->
      case lte _1 _2 of
        False ->
          case lte _0 _1 of
            False -> (_2, _1, _0)
            True ->
              case lte _0 _2 of
                False -> (_2, _0, _1)
                True -> (_0, _2, _1)
        True ->
          case lte _0 _2 of
            False ->
              case lte _2 _1 of
                False -> (_1, _2, _0)
                True -> (_2, _1, _0)
            True ->
              case lte _0 _1 of
                False -> (_1, _0, _2)
                True -> wild_X8
```

Fantastic! When we specialize to `Int`{.haskell}, we get all of the proper unpacking:
 
```haskell
sort3Int :: (Int, Int, Int) -> (Int, Int, Int)
sort3Int = inline sort3 (<=)
```

Core (with just the variable names cleaned up this time):

```haskell
sort3Int
  = \ (w :: (Int, Int, Int)) ->
      case w of w_X { (_0, _1, _2) ->
      case _0 of w_0 { GHC.Types.I# _0U ->
      case _1 of w_1 { GHC.Types.I# _1U ->
      case _2 of w_2 { GHC.Types.I# _2U ->
      case GHC.Prim.<=# _1U _2U of {
        __DEFAULT ->
          case GHC.Prim.<=# _0U _1U of {
            __DEFAULT -> (w_2, w_1, w_0);
            1# ->
              case GHC.Prim.<=# _0U _2U of {
                __DEFAULT -> (w_2, w_0, w_1);
                1# -> (w_0, w_2, w_1)
              }
          };
        1# ->
          case GHC.Prim.<=# _0U _2U of {
            __DEFAULT ->
              case GHC.Prim.<=# _2U _1U of {
                __DEFAULT -> (w_1, w_2, w_0);
                1# -> (w_2, w_1, w_0)
              };
            1# ->
              case GHC.Prim.<=# _0U _1U of {
                __DEFAULT -> (w_1, w_0, w_2);
                1# -> w_X
              }
          }
      }
      }
      }
      }
      }
```

Now, for the real test: sorting 5-tuples, using the network above.

```haskell
sort5 :: (a -> a -> Bool) -> (a,a,a,a,a) -> (a,a,a,a,a)
sort5 lte (_0,_1,_2,_3,_4)
    = swap2 lte _0 _1 $ \ _0 _1 ->
      swap2 lte _2 _3 $ \ _2 _3 ->
      swap2 lte _0 _2 $ \ _0 _2 ->
      swap2 lte _1 _3 $ \ _1 _3 ->
      swap2 lte _1 _2 $ \ _1 _2 ->
      swap2 lte _0 _4 $ \ _0 _4 ->
      swap2 lte _1 _4 $ \ _1 _4 ->
      swap2 lte _2 _4 $ \ _2 _4 ->
      swap2 lte _3 _4 $ \ _3 _4 ->
      (_0,_1,_2,_3,_4)
{-# INLINE sort5 #-}
```

The core output from this is over 1000 lines long: you can see it (with the variable names cleaned up) [here](https://gist.github.com/oisdk/ec25d76d918135c4c28777e1b84ead5f).

In my benchmarks, these functions are indeed quicker than their counterparts in vector, but I'm not confident in my knowledge of Haskell performance to make much of a strong statement about them.
