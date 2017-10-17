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

As you'll notice, the result of the two operations above is the same (6; although one may take much longer than the other). In fact, *whenever* the result of `foldr`{.haskell} and `foldl`{.haskell} is the same for a pair of arguments (in this case `+`{.haskell} and `0`{.haskell}), we say that that pair forms a [`Monoid`{.haskell}](https://hackage.haskell.org/package/base-4.10.0.0/docs/Data-Monoid.html#t:Monoid) for some type (well, there's some extra stuff to do with `0`{.haskell}, but I only care about associativity at the moment). In this case, the [`Sum`{.haskell}](https://hackage.haskell.org/package/base-4.10.0.0/docs/Data-Monoid.html#t:Sum) monoid is formed:

```{.haskell}
newtype Sum a = Sum { getSum :: a }

instance Num a => Monoid (Sum a) where
  mempty = Sum 0
  mappend (Sum x) (Sum y) = Sum (x + y)
```

When you know that you have a monoid, you can use the [`foldMap`{.haskell}](https://hackage.haskell.org/package/base-4.10.0.0/docs/Data-Foldable.html#v:foldMap) function: this is the third kind of fold. It says that you don't care which of `foldl`{.haskell} or `foldr`{.haskell} is used, so the implementer of `foldMap`{.haskell} can put the parentheses wherever they want:

```{.haskell}
foldMap Sum [1,2,3]
(1 + 2) + (3 + 0)
0 + ((1 + 2) + 3)
((0 + 1) + 2) + 3
```

And we can't tell the difference from the result. This is a pretty bare-bones introduction to folds and monoids: you won't need to know more than that for the rest of this post, but the topic area is fascinating and deep, so don't let me give you the impression that I've done anything more than scratched the surface.

# Other Ways to Fold

Quite often, we *do* care about where the parentheses go. Take, for instance, a binary tree type, with values at the leaves:

```{.haskell}
data Tree a
  = Empty
  | Leaf a
  | Tree a :*: Tree a

instance Show a =>
         Show (Tree a) where
    showsPrec n Empty = showString "()"
    showsPrec n (Leaf x) = showsPrec n x
    showsPrec n (l :*: r) =
        showParen (n > 5) (showsPrec 6 l . showChar '*' . showsPrec 6 r)
```

We can't (well, shouldn't) us `foldMap`{.haskell} here, because we would be able to tell the difference between different arrangements of parentheses:

```{.haskell}
foldMap something [1,2,3]
(1*2)*(3*())
()*((1*2)*3)
((()*1)*2)*3
```

So we use one of the folds which lets us choose the arrangements of parentheses:

```{.haskell}
(foldr (:*:) Empty . map Leaf) [1,2,3,4,5,6]
-- 1*(2*(3*(4*(5*(6*())))))

(foldl (:*:) Empty . map Leaf) [1,2,3,4,5,6]
-- (((((()*1)*2)*3)*4)*5)*6
```

The issue is that neither of the trees generated are necessarily what we want: often, we want something more *balanced*.

## TreeFold

To try and find a better fold, let's (for now) assume we're always going to get non-empty input. This will let us simplify the `Tree`{.haskell} type a little, to:

```{.haskell}
data Tree a
  = Leaf a
  | Tree a :*: Tree a
  deriving Foldable

instance Show a =>
         Show (Tree a) where
    showsPrec n (Leaf x) = showsPrec n x
    showsPrec n (l :*: r) =
        showParen (n > 5) (showsPrec 6 l . showChar '*' . showsPrec 6 r)
```

Then, we can use Jon Fairbairn's fold described in [this](http://www.mail-archive.com/haskell@haskell.org/msg01788.html) email, adapted a bit for our non-empty input:

```{.haskell}
import Data.List.NonEmpty (NonEmpty(..))

treeFold :: (a -> a -> a) -> NonEmpty a -> a
treeFold f = go
  where
    go (x :| []) = x
    go (a :| b:l) = go (f a b :| pairMap l)
    pairMap (x:y:rest) = f x y : pairMap rest
    pairMap xs = xs
```

There are two parts to this function: `pairMap`{.haskell} and the `go`{.haskell} helper. `pairMap`{.haskell} combines adjacent elements in the list using the combining function. As a top-level function it might look like this:

```{.haskell}
pairMap f (x:y:rest) = f x y : pairMap f rest
pairMap f xs = xs

pairMap (++) ["a","b","c","d","e"]
-- ["ab","cd","e"]
```

As you can see, it leaves any leftovers untouched at the end of the list.

The `go`{.haskell} helper applies `pairMap`{.haskell} repeatedly to the list until it has only one element. This gives us much more balanced results that `foldl`{.haskell} or `foldr`{.haskell} (turn on `-XOverloadedLists`{.haskell} to write non-empty lists using this syntax):

```{.haskell}
(treeFold (:*:) . fmap Leaf) [1,2,3,4,5,6]
-- ((1*2)*(3*4))*(5*6)

(treeFold (:*:) . fmap Leaf) [1,2,3,4,5,6,7,8]
-- ((1*2)*(3*4))*((5*6)*(7*8))
```

However, there are still cases where one branch will be much larger than its sibling. The fold fills a balanced binary tree from the left, but any leftover elements are put at the top level. In other words:

```{.haskell}
(treeFold (:*:) . fmap Leaf) [1..9]
-- (((1*2)*(3*4))*((5*6)*(7*8)))*9
```

That `9`{.haskell} hanging out on its own there is a problem.

## Zigzagging

One observation we can make is that `pairMap`{.haskell} always starts from the same side on each iteration, like a typewriter moving from one line to the next. This has the consequence of building up the leftovers on one side, leaving them until the top level.

We can improve the situation slightly by going back and forth, slalom-style, so we consume leftovers on each iteration:

```{.haskell}
treeFold :: (a -> a -> a) -> NonEmpty a -> a
treeFold f = goTo where
  
  goTo (y :| []) = y
  goTo (a :| b : rest) = goFro (pairMap f (f a b) rest)
  goFro (y :| []) = y
  goFro (a :| b : rest) = goTo (pairMap (flip f) (f b a) rest)

  pairMap f = go [] where
    go ys y (a:b:rest) = go (y:ys) (f a b) rest
    go ys y [z] = z :| y : ys
    go ys y [] = y :| ys
```

Notice that we have to flip the combining function to make sure the ordering is the same on output. For the earlier example, this solves the issue:

```{.haskell}
(treeFold (:*:) . fmap Leaf) [1..9]
-- ((1*2)*((3*4)*(5*6)))*((7*8)*9)
```

It does *not* build up the tree as balanced as it possibly could, though:

```{.haskell}
(treeFold (:*:) . fmap Leaf) [1,2,3,4,5,6]
-- (1*2)*((3*4)*(5*6))
```

There's four elements in the right branch, and two in the left in the above example. Three in each would be optimal.

Wait—optimal in what sense, exactly? What do we mean when we say one tree is more balanced than another? Let's say the "balance factor" is the largest difference in size of two sibling trees:

```{.haskell}
balFac :: Tree a -> Integer
balFac = fst . go where
  go :: Tree a -> (Integer, Integer)
  go (Leaf _) = (0, 1)
  go (l :*: r) = (lb `max` rb `max` abs (rs - ls), rs + ls) where
    (lb,ls) = go l
    (rb,rs) = go r
```

And one tree is more balanced than another if it has a smaller balance factor. From what I can tell, according to this definition, the slalom method is always more balanced than the typewriter for lists of the same length. I haven't been able to verify this formally, but from some quick experiments and some help from [oeis.org](https://oeis.org/), all trees of size smaller than $2^n$ (or, to put it another way, all trees with depth less than $n$) will have a balance factor less than the $n$th [Jacobsthal number](https://oeis.org/A001045). Interestingly, that's (apparently) also the number of ways to tie a tie using $n + 2$ turns.


Jacobsthal numbers are defined like this:

```{.haskell}
j 0 = 0
j 1 = 1
j n = j (n-1) + 2 * j (n-2)
```

Which kind of makes sense: the worst case for balancedness is lists of size $2^n+1$. When this happens, there's an imbalance at every iteration of `pairFold`{.haskell}. So, at the top level, there's the imbalance caused by the second-last `pairFold`{.haskell}, plus the imbalance caused by the third-to-last. However, the second imbalance is twice what it was at that level, because it is now working with an already-paired-up list. Why isn't the second last imbalance also doubled? Because it's counteracted by the fact that we turned around: the imbalance is in an element that's a leftover element. At least that's what my intuition is at this point.

The minimum balance factor is, of course, one. Unfortunately, to achieve that, I lost some of the properties of the previous folds:

## Lengths

Up until now, I have been avoiding taking the length of the incoming list. It would lose a lot of laziness, cause an extra traversal, and generally seems like an ugly solution. Nonetheless, it gives the most balanced results I could find so far:

```{.haskell}
treeFold :: (a -> a -> a) -> NonEmpty a -> a
treeFold f (x:|xs) = go (length (x:xs)) (x:xs) where
  go 1 [y] = y
  go n ys = f (go m a) (go (n-m) b) where
    (a,b) = splitAt m ys 
    m = n `div` 2
```

`splitAt`{.haskell} is an inefficient operation, but if we let the left-hand call return its unused input from the list, we can avoid it:

```{.haskell}
treeFold :: (a -> a -> a) -> NonEmpty a -> a
treeFold f (x:|xs) = fst (go (length (x:xs)) (x:xs)) where
  go 1 (y:ys) = (y,ys)
  go n ys = (f l r, rs) where
    (l,ls) = go m ys
    (r,rs) = go (n-m) ls
    m = n `div` 2
```

Finally, you may have spotted the state monad in this last version. We can make the similarity explicit:

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

And there you have it: three different ways to fold in a more balanced way. Perhaps surprisingly, the first is the fastest in my tests. I'd love to hear if there's a more balanced version (which is lazy, ideally) that is just as efficient as the first implementation.

# Stable Summation

I have found two other uses for these folds other than simply constructing more balanced binary trees. The first is summation of floating-point numbers. If you sum floating-point numbers in the usual way with `foldl'`{.haskell} (or, indeed, with an accumulator in an imperative language), you will see an error growth of $\mathcal{O}(n)$, where $n$ is the number of floats you're summing.

A well-known solution to this problem is the [Kahan summation algorithm](https://en.wikipedia.org/wiki/Kahan_summation_algorithm). It carries with it a running compensation for accumulating errors, giving it $\mathcal{O}(1)$ error growth. There are two downsides to the algorithm: it takes four times the number of numerical operations to perform, and isn't parallel.

For that reason, it's often not used in practice: instead, floats are summed *pairwise*, in a manner often referred to as [cascade summation](https://en.wikipedia.org/wiki/Pairwise_summation). This is what's used in [NumPy](https://github.com/numpy/numpy/pull/3685). The error growth isn't quite as good—$\mathcal{O}(\log{n})$—but it takes the exact same number of operations as normal summation. On top of that:

# Parallelization

Dividing a fold into roughly-equal chunks is exactly the kind of problem encountered when trying to parallelize certain algorithms. Adapting the folds above so that their work is performed in parallel is surprisingly easy:

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

The above will split the fold into `numCapabilities`{.haskell} chunks, and perform each one in parallel. `numCapabilities`{.haskell} is a constant defined in [GHC.Conc](https://hackage.haskell.org/package/base-4.10.0.0/docs/GHC-Conc.html): it's the number of threads which can be run simultaneously at any one time. Alternatively, you could the function include a parameter for how many chunks to split the computation into. As it is, I think it's pretty cool that code like this:

```{.haskell}
treeFoldParallel (+) [1..10000]
```

Will just figure out how many cores your machine has, split the input into that many chunks, and perform a somewhat-stable summation algorithm on it.

All of this is provided in a [library](https://hackage.haskell.org/package/treefold) I've put up on Hackage.
