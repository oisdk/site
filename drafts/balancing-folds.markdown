---
title: Balancing Folds
tags: Haskell, Folds
---

There are three main ways to fold things in Haskell: from the right, from the left, and from either side. Let's look at the left vs right variants first. `foldr`{.haskell} works from the right:

```{.haskell}
foldr (+) 0 [1,2,3]
1 + (2 + (3 + 0))
```

And `foldl`{.haskell} from the left:

```{.haskell}
foldl (+) 0 [1,2,3]
((0 + 1) + 2) + 3
```

As you'll notice, the result of the two operations above is the same (although one may take much longer than the other). In fact, *whenever* the result of `foldr`{.haskell} and `foldl`{.haskell} is the same for a pair of arguments (in this case `+`{.haskell} and `0`{.haskell}), we say that that pair forms a [`Monoid`{.haskell}](https://hackage.haskell.org/package/base-4.10.0.0/docs/Data-Monoid.html#t:Monoid) for some type. In this case, the [`Sum`{.haskell}](https://hackage.haskell.org/package/base-4.10.0.0/docs/Data-Monoid.html#t:Sum) monoid is formed:

```{.haskell}
newtype Sum a = Sum { getSum :: a }

instance Num a => Monoid (Sum a) where
  mempty = Sum 0
  mappend (Sum x) (Sum y) = Sum (x + y)
```

When you know that you have a monoid, you can use the `foldMap`{.haskell} function: this is the third kind of fold. It says that you don't care which of `foldl`{.haskell} or `foldr`{.haskell} is used, so the implementer of `foldMap`{.haskell} can choose which is more efficient (or some combination of the two).

This is a pretty bare-bones introduction to folds and monoids: you won't need to know more than that for the rest of this post, but the topic area is fascinating and deep, so don't let me give you the impression that I've done anything more than scratched the surface.

# Other Ways to Fold

Quite often, we *do* care about whether we choose `foldl`{.haskell} or `foldr`{.haskell}. Take, for instance, a binary tree type, with values at the leaves:

```{.haskell}
data Tree a
  = Empty
  | Leaf a
  | Tree a :*: Tree a
  deriving Show
```

The results of `foldl`{.haskell} and `foldr`{.haskell} look very different indeed for this type:

```{.haskell}
(foldr (:*:) Empty . map Leaf) [1,2,3]
-- Leaf 1 :*: (Leaf 2 :*: (Leaf 3 :*: Empty))

(foldl (:*:) Empty . map Leaf) [1,2,3]
-- ((Empty :*: Leaf 1) :*: Leaf 2) :*: Leaf 3
```

Also, if we were constructing a tree, we probably wouldn't want *either* of those results above: they're both totally unbalanced.

To try and find a better fold, let's (for now) assume we're always going to get non-empty input. This will let us simplify the `Tree`{.haskell} type a little, to:

```{.haskell}
data Tree a
  = Leaf a
  | Tree a :*: Tree a
  deriving Show
```

Then, we can use a fold described in [this](http://www.mail-archive.com/haskell@haskell.org/msg01788.html) email, adapted a bit for our non-empty input:

```{.haskell}
import Data.List.NonEmpty (NonEmpty(..))

treeFold :: (a -> a -> a) -> NonEmpty a -> a
treeFold f = go
  where
    go (x :| []) = x
    go (a :| b:l) = go (f a b :| pairFold l)
    pairFold (x:y:rest) = f x y : pairFold rest
    pairFold xs = xs
```

And we get much more balanced results:

```{.haskell}
(treeFold (:*:) . fmap Leaf) (1 :| [2,3])
--  (Leaf 1 :*: Leaf 2) :*: Leaf 3

(treeFold (:*:) . fmap Leaf) (1 :| [2,3,4])
-- (Leaf 1 :*: Leaf 2) :*: (Leaf 3 :*: Leaf 4)
```

However, there are still cases where one branch will be much larger than its sibling. The fold fills a balanced binary tree from the left, but any leftover elements are put at the top level. In other words:

```{.haskell}
(treeFold (:*:) . fmap Leaf) (1 :| [2,3,4,5])
-- ((Leaf 1 :*: Leaf 2) :*: (Leaf 3 :*: Leaf 4)) :*: Leaf 5
```

The main issue is that every run of `pairFold`{.haskell} keeps its leftovers on the same side: we can improve the situation slightly by alternating:

```{.haskell}
treeFold :: (a -> a -> a) -> NonEmpty a -> a
treeFold f = goFor where
  
  goFor (y :| []) = y
  goFor (a :| b : rest) = goBack (pairMap f (f a b) rest)
  goBack (y :| []) = y
  goBack (a :| b : rest) = goFor (pairMap (flip f) (f b a) rest)

  pairMap f = go [] where
    go ys y (a:b:rest) = go (y:ys) (f a b) rest
    go ys y [z] = z :| y : ys
    go ys y [] = y :| ys
```

The `pairMap`{.haskell} here builds up its list in reverse, so it puts its leftovers on a different side on each iteration. Notice that we have to flip the combining function to make sure the ordering is the same on output. For the earlier example, this solves the issue:

```{.haskell}
(treeFold (:*:) . fmap Leaf) (1 :| [2,3,4,5])
-- (Leaf 1 :*: Leaf 2) :*: ((Leaf 3 :*: Leaf 4) :*: Leaf 5)
```

It does *not* build up the tree as balanced as it possibly could, though:

```{.haskell}
(treeFold (:*:) . fmap Leaf) (1 :| [2,3,4,5,6])
-- (Leaf 1 :*: Leaf 2) :*: ((Leaf 3 :*: Leaf 4) :*: (Leaf 5 :*: Leaf 6))
```

How balanced is the resulting tree, exactly? I haven't been able to verify this formally, but from some quick experiments and some help from [oeis.org](https://oeis.org/), it looks like a tree of depth $n$ will have a difference in size of its immediate subtrees of at most the $n$th [Jacobsthal number](https://oeis.org/A001045). Better than the last attempt, but not ideal.

Up until now, I have been avoiding taking the length of the incoming list. It would prevent infinite lists from being used, and seems like an ugly solution. Nonetheless, it gives the most balanced results I could find so far:

```{.haskell}
treeFold :: (a -> a -> a) -> NonEmpty a -> a
treeFold f (x:|xs) = go (length (x:xs)) (x:xs) where
  go 1 [y] = y
  go n ys = f (go m a) (go (n-m) b) where
    (a,b) = splitAt m ys 
    m = n `div` 2
```

The call to `splitAt`{.haskell} is inefficient, but luckily avoidable:

```{.haskell}
treeFold :: (a -> a -> a) -> NonEmpty a -> a
treeFold f (x:|xs) = fst (go (length (x:xs)) (x:xs)) where
  go 1 (y:ys) = (y,ys)
  go n ys = (f l r, rs) where
    (l,ls) = go m ys
    (r,rs) = go (n-m) ls
    m = n `div` 2
```

Finally, you may have recognized the state monad above:

```{.haskell}
treeFold :: (a -> a -> a) -> NonEmpty a -> a
treeFold f (x:|xs) = evalState (go (length (x:xs))) (x:xs) where
  go 1 = state (\(y:ys) -> (y,ys))
  go n = do
    let m = n `div` 2
    l <- go m
    r <- go (n-m)
    return (f l r)
```

And there you have it: three different ways to fold in a more balanced way. Perhaps surprisingly, the first is the most efficient in my tests. 

# Stable Summation

I have found two other uses for these folds other than simply constructing more balanced binary trees. The first is summation of floating-point numbers. If you sum floating-point numbers in the usual way, with `foldl`{.haskell}, you will see an error growth of $O(n)$, where $n$ is the length of the sequence. However, summing them pairwise only gives an error growth of $O(\log n)$. In practice, you're probably better off using the [Kahan summation algorithm](https://en.wikipedia.org/wiki/Kahan_summation_algorithm) (which has $O(1)$ error growth), but there's one reason you may prefer the pairwise solution:

# Parallelization

Dividing a fold into roughly-equal chunks is exactly the kind of problem encountered when trying to parallelize certain algorithms. These folds can be easily adapted (without changing the original definitions) into parallel versions like so:

```{.haskell}
splitPar :: (a -> a -> a) -> (Int -> a) -> (Int -> a) -> Int -> a
splitPar f = go
  where
    go l r 0 = f (l 0) (r 0)
    go l r n = lt `par` (rt `pseq` f lt rt)
      where
        lt = l m
        rt = r m
        m = n `div` 2

treeFoldParallel :: (a -> a -> a) -> NonEmpty a -> a
treeFoldParallel f xs =
    treeFold const (splitPar f) xs numCapabilities
```

The above will split the fold into `numCapabilities`{.haskell} chunks, and perform each one in parallel. `numCapabilities`{.haskell} is a constant defined in [GHC.Conc](https://hackage.haskell.org/package/base-4.10.0.0/docs/GHC-Conc.html): it's the number of threads which can be run simultaneously at any one time. Alternatively, you could the function include a parameter for how many chunks to split the computation into.

All of this is provided in a [library](https://hackage.haskell.org/package/treefold) I've put up on Hackage.
