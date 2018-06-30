---
title: "Breadth-First Rose Trees: Traversals and the Cofree Comonad"
tags: Haskell
series: Breadth-First Traversals
bibliography: Rose Tree Traversals.bib
---

I was looking again at the issue of writing breadth-first traversals for rose trees, and in particular the problem explored in @gibbons_breadth-first_2015. The breadth-first traversal here is a traversal in the lensy sense.

First, let's look back at getting the levels out of the tree. Here's the old function I arrived at last time:

```haskell
levels :: Forest a -> [[a]]
levels ts = foldl f b ts [] []
  where
    f k (Node x xs) ls qs = k (x : ls) (xs : qs)

    b _ [] = []
    b k qs = k : foldl (foldl f) b qs [] []
```

After wrangling the definition a little, I got to the following (much cleaner) definition:

```haskell
levels :: Tree a -> [[a]]
levels tr = f tr [] where
  f (Node x xs) (y:ys) = (x:y) : foldr f ys xs
  f (Node x xs) []     = [x]   : foldr f [] xs
```

# Cofree

Before going any further, all of the functions so far can be redefined to work on the [cofree comonad](http://hackage.haskell.org/package/free-5.0.2/docs/Control-Comonad-Cofree.html):

```haskell
data Cofree f a = a :< f (Cofree f a)
```

When `f`{.haskell} is specialized to `[]`{.haskell}, we get the original rose tree. But what we actually require is much less specific: `levels`{.haskell}, for instance, only needs `Foldable`{.haskell}.

```haskell
levelsCofree :: Foldable f => Cofree f a -> [[a]]
levelsCofree tr = f tr []
  where
    f (x:<xs) (y:ys) = (x:y) : foldr f ys xs
    f (x:<xs) []     = [x]   : foldr f [] xs
```

Using this, we can write the efficient breadth-first traversal:

```haskell
breadthFirst
    :: (Applicative f, Traversable t)
    => (a -> f b) -> Cofree t a -> f (Cofree t b)
breadthFirst c (t:<ts) =
    liftA2 evalState (map2 (:<) (c t) (fill ts)) chld
  where
    chld = foldr (liftA2 evalState) (pure []) (foldr f [] ts)
    fill = traverse (const (state (\(x:xs) -> (x,xs))))

    f (x:<xs) (q:qs)
        = app2 (\y ys zs -> (y:<ys) : zs) (c x) (fill xs) q
        : foldr f qs xs
    f (x:<xs) []
        = map2 (\y ys -> [y:<ys]) (c x) (fill xs)
        : foldr f [] xs

    map2 k x xs = fmap   (\y -> fmap   (k y) xs) x
    app2 k x xs = liftA2 (\y -> liftA2 (k y) xs) x
```

At every level, the subforest's shape it taken (`fill`{.haskell}), and it's traversed recursively. We can fuse these two steps into one:

```haskell
breadthFirst
    :: (Traversable t, Applicative f)
    => (a -> f b) -> Cofree t a  -> f (Cofree t b)
breadthFirst c (t:<ts) =
    liftA2
        evalState
        (map2 (:<) (c t) fill)
        (foldr (liftA2 evalState) (pure []) (chld []))
  where
    Compose (Endo chld,fill) = go ts

    go = traverse (\x -> Compose (Endo (f x), state (\(y:ys) -> (y,ys))))

    f (x:<xs) (q:qs) = app2 (\y ys zs -> (y:<ys) : zs) (c x) r q : rs qs
      where Compose (Endo rs,r) = go xs
    f (x:<xs) [] = map2 (\y ys -> [y:<ys]) (c x) r : rs []
      where Compose (Endo rs,r) = go xs

    map2 k x xs = fmap   (\y -> fmap   (k y) xs) x
    app2 k x xs = liftA2 (\y -> liftA2 (k y) xs) x
```

The overhead from this approach scraps any benefit, though.
