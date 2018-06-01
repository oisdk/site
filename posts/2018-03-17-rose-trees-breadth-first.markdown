---
title: Rose Trees, Breadth-First
tags: Haskell, Trees
series: Breadth-First Traversals
bibliography: Rose Tree Traversals.bib
---

In contrast to the more common binary trees, in a rose tree every node can have any number of children.

```haskell
data Tree a
    = Node
    { root   :: a
    , forest :: Forest a
    }

type Forest a = [Tree a]
```

One of the important manipulations of this data structure, which forms the basis for several other algorithms, is a breadth-first traversal. I'd like to go through a couple of techniques for implementing it, and how more generally you can often get away with using much simpler data structures if you really pinpoint the API you need from them.

As a general technique, @okasaki_breadth-first_2000 advises that a queue be used:

```haskell
breadthFirst :: Tree a -> [a]
breadthFirst tr = go (singleton tr)
  where
    go q = case pop q of
      Nothing -> []
      Just (Node x xs,qs) -> x : go (qs `append` xs)
```

There are three functions left undefined there: `singleton`{.haskell}, `pop`{.haskell}, and `append`{.haskell}. They represent the API of our as-of-yet unimplemented queue, and their complexity will dictate the complexity of the overall algorithm. As a (bad) first choice, we could use simple lists, with the functions defined thus:

```haskell
singleton x = [x]
pop (x:xs) = Just (x,xs)
pop [] = Nothing
append = (++)
```

Those repeated appends are bad news. The queue needs to be able to support popping from one side and appending from the other, which is something lists absolutely *cannot* do well.

We could swap in a more general queue implementation, possibly using Data.Sequence, or a pair of lists. But these are more complex and general than we need, so let's try and pare down the requirements a little more.

First, we don't need a pop: the go function can be expressed as a fold instead. Second, we don't need *every* append to be immediately stuck into the queue, we can batch them, first appending to a structure that's efficient for appends, and then converting that to a structure which is efficient for folds. In code:

```haskell
breadthFirst :: Forest a -> [a]
breadthFirst ts = foldr f b ts []
  where
    f (Node x xs) fw bw = x : fw (xs : bw)

    b [] = []
    b qs = foldl (foldr f) b qs []
```

We're consing instead of appending, but the consumption is being done in the correct direction anyway, because of the `foldl`{.haskell}.

## Levels

So next step: to get the `levels`{.haskell} function from Data.Tree. Instead of doing a breadth-first traversal, it returns the nodes at each *level* of the tree. Conceptually, every time we did the reverse above (called `foldl`{.haskell}), we will do a cons as well:

```haskell
levels :: Forest a -> [[a]]
levels ts = foldl f b ts [] []
  where
    f k (Node x xs) ls qs = k (x : ls) (xs : qs)

    b _ [] = []
    b k qs = k : foldl (foldl f) b qs [] []
```

## Unfolding

The original reason I started work on these problems was [this](https://github.com/haskell/containers/issues/124) issue in containers. It concerns the [`unfoldTreeM_BF`](https://hackage.haskell.org/package/containers-0.5.11.0/docs/Data-Tree.html#v:unfoldTreeM_BF) function. An early go at rewriting it, inspired by levels above, looks like this:

```{.haskell .numberLines}
unfoldForestM_BF :: Monad m => (b -> m (a, [b])) -> [b] -> m (Forest a)
unfoldForestM_BF f ts = b [ts] (const id)
  where
    b [] k = pure (k [] [])
    b qs k = foldl (foldr t) b qs [] (\x -> k [] . foldr (uncurry run) id x)

    t a fw bw k = do
        (x,cs) <- f a
        let !n = length cs
        fw (cs : bw) (k . (:) (x, n))

    run x n xs ys =
      case splitAt n ys of
          (cs,zs) -> Node x cs : xs zs
```

It basically performs the same this as the levels function, but builds the tree back up in the end using the `run`{.haskell} function. In order to do that, we store the length of each subforest on line 9, so that each node knows how much to take from each level.

A possible optimization is to stop taking the length. Anything in list processing that takes a length screams "wrong" to me (although it's not always true!) so I often try to find a way to avoid it. The first option would be to keep the `cs`{.haskell} on line 8 around, and use *it* as an indicator for the length. That keeps it around longer than strictly necessary, though. The other option is to add a third level: for `breadthFirst`{.haskell} above, we had one level; for `levels`{.haskell}, we added another, to indicate the structure of the nodes and their subtrees; here, we can add a third, to maintain that structure when building back up:

```haskell
unfoldForestM_BF :: Monad m => (b -> m (a, [b])) -> [b] -> m (Forest a)
unfoldForestM_BF f ts = b [ts] (\ls -> concat . ls)
  where
    b [] k = pure (k id [])
    b qs k = foldl g b qs [] (\ls -> k id . ls)

    g a xs qs k = foldr t (\ls ys -> a ys (k . run ls)) xs [] qs

    t a fw xs bw = f a >>= \(x,cs) -> fw (x:xs) (cs:bw)

    run x xs = uncurry (:) . foldl go ((,) [] . xs) x
      where
        go ys y (z:zs) = (Node y z : ys', zs')
          where
            (ys',zs') = ys zs
```

This unfortunately *slows down* the code.
