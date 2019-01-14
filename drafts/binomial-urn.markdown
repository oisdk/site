---
title: A Binomial Urn
tags: Haskell
series: Balanced Folds
bibliography: Tree Folds.bib
---

When we started the series, we wanted to find a "better" fold: one that was more
balanced than either `foldl` or `foldr` (in its placement of parentheses). Both
of these are about as unbalanced as you can get:

```haskell
>>> foldr (+) 0 [1,2,3]
1 + (2 + (3 + 0))
>>> foldl (+) 0 [1,2,3]
((0 + 1) + 2) + 3
```

The first better fold solution was Jon Fairbairn's  simple `treeFold`:

```haskell
treeFold :: (a -> a -> a) -> a -> [a] -> a
treeFold f = go
  where
    go x [] = x
    go a  (b:l) = go (f a b) (pairMap l)
    pairMap (x:y:rest) = f x y : pairMap rest
    pairMap xs = xs
  
>>> treeFold (+) 0 [1,2,3]
(0 + 1) + (2 + 3)
```

Already this function was kind of magical: if your binary operator merges two
sorted lists, `foldr` will give you insertion sort, whereas `treeFold` will give
you merge sort; for summing floats, `treeFold` has a lower error growth than
`sum`. By dividing up the work better, we were able to improve the
characteristics of many algorithms automatically. We also saw that it could
easily be made parallel:

```haskell
parseq :: a -> b -> b
parseq a b =
    runST
        (bool (par a b) (seq a b) <$>
         unsafeIOToST (liftA2 (>) numSparks getNumCapabilities))

treeFoldParallel :: (a -> a -> a) -> a -> [a] -> a
treeFoldParallel f =
    treeFold
        (\l r ->
              r `parseq` (l `parseq` f l r))
```

In the next post, we saw how we could make the fold incremental, by using binary
number representations for data structures. This let us do 2 things: it meant
the fold was structurally terminating, so it would pass the termination checker
(efficiently) in languages like Agda or Idris, and it meant we could write
`scanl` using the fold. The `scanl` was also efficient: you could run the fold
at any point in $\mathcal{O}(\log n)$ time, and work would be shared between
subsequent runs. Effectively, this let us use it to solve greedy optimization
problems. We also saw how it was effectively constructing an implicit binomial
heap under the hood, and how it exploited laziness to get sharing.

I've gotten huge mileage out of this fold and the general ideas about it, and
today I'm going to show one more use of it. We're going to improve upon the data
structure presented in @lampropoulos_ode_2017.

# A Random Urn

The paper opens with the problem:

> Suppose you have an urn containing two red balls, four green balls, and three
> blue balls. If you take three balls out of the urn, what is the probability
> that two of them are green?

If you were to take just *one* ball out of the earn, calculating the associated
probabilities would be easy. Once you get to the second, though, you have to
update the previous probability *based on what ball was removed*. In other
words, we need to be able to dynamically update the distribution.

Using lists, this would obviously become an $\mathcal{O}(n)$ operation. In the
paper, an almost-perfect binary tree is used. This turns the operation into one
that's $\mathcal{O}(\log n)$. The rest of the operations have the following
complexities:

Operation   Complexity
----------  ----------
`insert`    $\mathcal{O}(\log n)$
`remove`    $\mathcal{O}(\log n)$
`fromList`  $\mathcal{O}(n)$

As a quick spoiler, the improved version presented here has these complexities:

Operation   Complexity
---------   ----------
`insert`    $\mathcal{O}(1)$
`remove`    $\mathcal{O}(\log n)$
`merge`     $\mathcal{O}(\log n)$
`fromList`  $\mathcal{O}(n)$


We add another operation (`merge`), which means that the new structure is viable
as an instance of `Alternative`, `Monad`, and so on, making it an efficient
monad for weighted backtracking search.

# Heaps

The key thing to notice in the paper which will let us improve the structure is
that what they're designing is actually a *heap*. Well, a weird looking heap,
but a heap nonetheless.

Think about it like a max-heap (pop returns the largest element first), with a
degree of "randomization". In other words, when you go to do a pop, all of the
comparisons between the ordering keys (the weights in this case) sprinkles some
randomness into the equation, meaning that instead of `1 < 2` returning `True`,
it returns `True` $\frac{2}{3}$ of the time, and `False` the other
$\frac{1}{3}$.

This way of doing things means that not every heap is suitable: we want to run
comparisons at `pop` time (not `insert`), so a heap that stores the smallest
element at the top won't do. Since this is the majority of heaps, we're not left
with a huge amount to choose from.

The one presented in the paper is something like a Braun heap: the
$\mathcal{O}(n)$ `fromList` implementation is reminiscent of the one in
@okasaki_three_1997.

So what heap can we choose to get us the desired efficiency? Why, a binomial one
of course!

# Weighted Reservoir Sampling

An incredibly useful algorithm to know is *reservoir sampling*. It solves the
following problem:

> Choose a random item from a list, in one pass, without knowing the length of
> the list.

You might want to give it a go with a pen and paper before looking at the
solution. No? Ah, well.

```haskell
choose :: RandomGen g =>  [a] -> g -> (a, g)
choose [] = error "Empty list given to choose"
choose (x:xs) = foldr f (const (,)) xs (1 :: Word) x
  where
    f x a c y g = case randomR (0,c) g of
      (0,g') -> a (c+1) x g'
      (_,g') -> a (c+1) y g'
```

The basic idea is this: the function walks over the list, carrying some chosen
element it's seen so far, and the number of elements it's seen so far. When it
hits a new element, it *replaces* the chosen one with it with a probability of
$\frac{1}{n+1}$ where $n$ is the number of elements seen so far. The rest of the
elements after this one undergo the same test, each with decreasing
probabilities that they will be swapped in. Upgrading it to a weighted version
isn't too difficult:

```haskell
choose :: RandomGen g =>  [(a,Word)] -> g -> (a, g)
choose [] = error "Empty list given to choose"
choose ((x',i'):xs) = foldr f (const (,)) xs (i' - 1) x'
  where
    f (x,i) a j y g = case randomR (0,k) g of
        (q,g')
          | q < i     -> a k x g'
          | otherwise -> a k y g'
      where
        k = i + j
```

It's worth noting that this function is very related to the implementation of
the weighted random shuffle presented in the last post.

This is the function we are going to use to build our heap. Since it's linear
over a list, it's a good candidate for chunking: breaking the list into
pre-computed sections, which we then run the function on. These pre-computed
sections are going to be very similar to the trees described in the Urn paper:
by breaking them up, though, we get our $\mathcal{O}(1)$ `insert`, and
$\mathcal{O}(\log n)$ merge.

# The Data Structure

The urn structure itself is as follows:

```haskell
data Tree a
  = Tree
  { weight :: {-# UNPACK #-} !Word
  , branch :: Node a
  }
  
data Node a
  = Leaf a
  | Branch (Tree a) (Node a)

data Urn a
  = Urn {-# UNPACK #-} !Word (Tree a) (List a)
  
data List a
  = Nil
  | Cons {-# UNPACK #-} !(Urn a)
```
