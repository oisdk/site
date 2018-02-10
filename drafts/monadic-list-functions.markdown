---
title: Monadic List Functions
tags: Haskell, applicative
bibliography: Monadic List Functions.bib
---


Here's an old Haskell chestnut:

```haskell
>>> filterM (\_ -> [False, True]) [1,2,3]
[[],[3],[2],[2,3],[1],[1,3],[1,2],[1,2,3]]
```

`filterM (\_ -> [False,True])`{.haskell} gives the power set of some input list. It's one of the especially magical demonstrations of monads. From a high-level perspective, it makes sense: for each element in the list, we want it to be present in one output, and not present in another. It's hard to see how it actually *works*, though. The (old[^new-filterm]) [source](https://hackage.haskell.org/package/base-4.7.0.0/docs/src/Control-Monad.html#filterM) for `filterM`{.haskell} doesn't help hugely, either:

[^new-filterm]: The definition has since been [updated](https://hackage.haskell.org/package/base-4.10.1.0/docs/src/Control.Monad.html#filterM) to more modern Haskell: it now uses a fold, and only requires `Applicative`{.haskell}. Updating the *other* functions here similarly is the subject of future post.

```haskell
filterM          :: (Monad m) => (a -> m Bool) -> [a] -> m [a]
filterM _ []     =  return []
filterM p (x:xs) =  do
   flg <- p x
   ys  <- filterM p xs
   return (if flg then x:ys else ys)
```

Again, elegant and beautiful (aside from the three-space indent), but opaque. Despite not really getting how it works, I was encouraged by its simplicity to try my hand at some of the other functions from Data.List.

## Grouping

Let's start with the subject of my [last post](2018-01-07-groupBy.html). Here's the implementation:

```haskell
groupBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy p xs = build (\c n ->
  let f x a q
        | q x = (x : ys, zs)
        | otherwise = ([], c (x : ys) zs)
        where (ys,zs) = a (p x)
  in snd (foldr f (const ([], n)) xs (const False)))
```

It translates over pretty readily:

```haskell
groupByM :: Applicative m => (a -> a -> m Bool) -> [a] -> m [[a]]
groupByM p xs =
  fmap snd (foldr f (const (pure ([], []))) xs (const (pure (False))))
  where
    f x a q = liftA2 st (q x) (a (p x)) where
      st b (ys,zs)
        | b = (x : ys, zs)
        | otherwise = ([], (x:ys):zs)
```

Let's try it with a similar example to `filterM`{.haskell}:

```haskell
>>> groupByM (\_ _ -> [False, True]) [1,2,3]
[[[1],[2],[3]],[[1],[2,3]],[[1,2],[3]],[[1,2,3]]]
```

It gives the partitions of the list!

## Sorting

So these monadic generalisations have been discovered before, several times over. There's even a [package](https://hackage.haskell.org/package/monadlist-0.0.2) with monadic versions of the functions in Data.List. Exploring this idea with a little more formality is the paper "All Sorts of Permutations" [@christiansen_all_2016], and accompanying presentation [on YouTube](https://www.youtube.com/watch?v=vV3jqTxJ9Wc). They show that the monadic version of sort produces permutations of the input list, and examine the output from different sorting algorithms. I won't reproduce the implementations here, but the paper is worth a read.

## State

So the examples above are very interesting and cool, but they don't necessarily have a place in real Haskell code. If you wanted to find the permutations, partitions, or power set of a list you'd probably use a more standard implementation. That's not to say that these monadic functions have no uses, though: especially when coupled with `State`{.haskell} they yield readable and fast implementations for certain tricky functions. `ordNub`{.haskell}, for instance:

```haskell
ordNub :: Ord a => [a] -> [a]
ordNub =
  flip evalState Set.empty .
  filterM
    (\x -> do
       flg <- gets (Set.notMember x)
       when flg (modify (Set.insert x))
       pure flg)
```

Alternatively, using a monadic version of `maximumOn`{.haskell}:

```haskell
maximumOnM :: (Applicative m, Ord b) => (a -> m b) -> [a] -> m (Maybe a)
maximumOnM p = (fmap . fmap) snd . foldl f (pure Nothing)
  where
    f a e = liftA2 g a (p e)
      where
        g Nothing q = Just (q, e)
        g b@(Just (o, y)) q
          | o < q = Just (q, e)
          | otherwise = b
```

You can write a one-pass `mostFrequent`{.haskell}:

```haskell
mostFrequent :: Ord a => [a] -> Maybe a
mostFrequent =
  flip evalState Map.empty .
  maximumOnM
    (\x -> maybe 1 succ <$> state (Map.insertLookupWithKey (const (+)) x 1))
```

## Decision Trees



## Applicative

You might notice that none of these "monadic" functions actually require a monad constraint: they're all applicative. There's a straightforward implementation that relies only on applicative for most of these functions, with a notable exception: sort. Getting *that* to work with just applicative is the subject of a future post.
