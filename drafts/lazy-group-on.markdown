---
title: Lazily Grouping in Haskell
tags: Haskell
---

Here's a cool trick:

```haskell
minimum :: Ord a => [a] -> a
minimum = head . sort
```

This is $\mathcal{O}(n)$ in Haskell, not $\mathcal{O}(n \log n)$ as you might
expect.
And this isn't because Haskell is using some weird linear-time sorting
algorithm; indeed, the following is $\mathcal{O}(n \log n)$:

```haskell
maximum :: Ord a => [a] -> a
maximum = last . sort
```

No: since the implementation of `minimum` above only demands the first element
of the list, and since `sort` has been carefully implemented, only a linear
amount of work will be done to retrieve it.

It's not easy to structure programs to have the same property as `sort` does
above: to be maximally lazy, such that unnecessary work is not performed.
Today I was working on a maximally lazy implementation of the following program:

```haskell
groupOn :: Eq k => (a -> k) -> [a] -> [(k,[a])]
groupOn = ...

>>> groupOn (`rem` 2) [1..5]
[(1,[1,3,5]),(0,[2,4])]

>>> groupOn (`rem` 3) [5,8,3,6,2]
[(2,[5,8,2]),(0,[3,6])]
```

This function groups the elements of a list according to some key function.
The desired behaviour here is a little subtle: we don't want to just group
adjacent elements, for instance.

```haskell
groupOn (`rem` 3) [5,8,3,6,2] ≢ [(2,[5,8]),(0,[3,6]),(2,[2])]
```

And we don't want to reorder the elements of the list by the keys:

```haskell
groupOn (`rem` 3) [5,8,3,6,2] ≢ [(0,[3,6]),(2,[5,8,2])]
```

These constraints make it especially tricky to make this function lazy.
In fact, at first glance, it seems impossible.
What should, for instance, `groupOn id [1..]` return?
It can't even fill out the first group, since it will never find another `1`.
However, it *can* fill out the first key.
And, in fact, the second.
And it can fill out the first element of the first group.
Precisely:

```haskell
groupOn id [1..] ≡ [(1,1:⊥), (2,2:⊥), (3,3:⊥), ...
```

Another example is `groupOn id (repeat 1)`, or `groupOn id (cycle [1,2,3])`.
These each have partially-defined answers:

```haskell
groupOn id (repeat 1)      ≡ (1,repeat 1):⊥

groupOn id (cycle [1,2,3]) ≡ (1,repeat 1):(2,repeat 2):(3,repeat 3):⊥
```

So there is some kind of well-defined lazy semantics for this function.
The puzzle I was interested in was defining an efficient implementation for this
semantics.

# The Slow Case

The first approximation to a solution I could think of is the following:

```haskell
groupOn :: Ord k => (a -> k) -> [a] -> [(k, [a])]
groupOn k = Map.toList . Map.fromListWith (++) . map (\x -> (k x, [x]))
```

In fact, if you don't care about laziness, this is probably the best solution:
it's $\mathcal{O}(n \log n)$, it performs well (practically as well as
asymptotically), and it has the expected results.

However, there are problems.
Primarily this solution cares about ordering, which we don't want.
We want to emit the results in the same order that they were in the original
list, and we don't necessarily want to require an ordering on the elements (for
the efficient solution we will relax this last constraint).

Instead, let's implement our own "map" type that is inefficient, but more
general.

```haskell
type Map a b = [(a,b)]

insertWith :: Eq a => (b -> b -> b) -> a -> b -> Map a b -> Map a b
insertWith f k v [] = [(k,v)]
insertWith f k v ((k',v'):xs)
  | k == k'   = (k',f v v') : xs
  | otherwise = (k',v') : insertWith f k v xs

groupOn :: Eq k => (a -> k) -> [a] -> [(k, [a])]
groupOn k = foldr (uncurry (insertWith (++))) [] . map (\x -> (k x, [x]))
```

The problem here is that it's not lazy enough.
`insertWith` is strict in its last argument, which means that using `foldr`
doesn't gain us anything laziness-wise.

There is some extra information we can use to drive the result: we know that the
result will have keys that are in the same order as they appear in the list,
with duplicates removed:

```haskell
groupOn :: Eq k => (a -> k) -> [a] -> [(k, [a])]
groupOn k xs = map _ ks
  where
    ks = map k xs
```

From here, we can get what the values should be from each key by filtering the
original list:

```haskell
groupOn :: Eq k => (a -> k) -> [a] -> [(k,[a])]
groupOn key xs = map (\k -> (k, filter ((k==) . key) xs)) (nub (map key xs))
```

Using a kind of Schwarzian transform yields the following slight improvement:

```haskell
groupOn :: Eq k => (a -> k) -> [a] -> [(k,[a])]
groupOn key xs = map (\k -> (k , map snd (filter ((k==) . fst) ks))) (nub (map fst ks))
  where
    ks = map (\x -> (key x, x)) xs
```

But this traverses the same list multiple times unnecessarily.

The following is much better:

```haskell
groupOn :: Eq k => (a -> k) -> [a] -> [(k,[a])]
groupOn key = go . map (\x -> (key x, x)) 
  where
    go [] = []
    go ((k,x):xs) = (k,x:map snd y) : go ys
      where
        (y,ys) = partition ((k==).fst) xs
```
