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

The urn structure itself is a pretty standard binomial heap:

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
  = Nil
  | Urn {-# UNPACK #-} !Word (Tree a) (Urn a)
```

By avoiding the usual `Skip` constructors you often see in a binomial heap we
save a huge amount of space. Instead, we store the "number of zeroes before this
bit". Another thing to point out is that only left branches in the trees store
their weight: the same optimization is made in the paper.

Insertion is not much different from insertion for a usual binomial heap,
although we don't need to do anything to merge the trees:

```haskell
insert :: Word -> a -> Urn a -> Urn a
insert i' x' = go 0 (Tree i' (Leaf x'))
  where
    go !i x Nil = Urn i x Nil
    go !i x (Urn 0 y ys) = go (i+1) (mergeTree x y) ys
    go !i x (Urn j y ys) = Urn i x (Urn (j-1) y ys)
   
mergeTree :: Tree a -> Tree a -> Tree a
mergeTree xs ys =
    Tree
      (weight xs + weight ys)
      (Branch xs (branch ys))
```

We *could* potentially get insertion from amortized $\mathcal{O}(1)$ to
worst-case $\mathcal{O}(1)$ by using skew binary instead of binary (in fact I am
almost sure it's possible), but then we'd lose the efficient merge. I'll leave
exploring that for another day.

Sampling (with replacement) combines reservoir sampling and binary search:
first, we use reservoir sampling to pick the correct tree from the top-level
list, and then we drill down into that tree with binary search. 

```haskell
sample :: RandomGen g => Urn a -> g -> Maybe (a, g)
sample Nil = const Nothing
sample (Urn _ x' xs') = Just . go xs' (weight x' - 1) x'
  where
    go Nil _ x g = go' (weight x - 1) (branch x) g
    go (Urn _ x xs) j y g = case randomR (0,k) g of
        (q,g')
          | q < i     -> go xs k x g'
          | otherwise -> go xs k y g'
      where
        i = weight x
        k = i + j
    go' _ (Leaf x) g = (x, g)
    go' i (Branch xs ys) g = case randomR (0,i) g of
        (q,g')
          | q < weight xs -> go' (weight xs - 1) (branch xs) g'
          | otherwise -> go' (i - weight xs) ys g'
```

So we're off to a good start, but `remove` is a complex operation. We take the
same route taken in the paper: first, we perform an "uncons"-like operation,
which pops out the last inserted element. Then, we randomly choose a point in
the tree (using the same logic as in `sample`), and replace it with the popped
element. Finally, we decrement the counter on the newly (randomly) chosen
element, and reinsert it if it's still bigger than 0[^extra-step].

[^extra-step]: There's one extra step I haven't mentioned: we also must allow
    the first element (the last inserted) to be chosen, so we run the
    random-number generator once to check if that's the element we want to
    choose.
    
```haskell
remove :: RandomGen g => Urn a -> g -> Maybe ((a, Urn a), g)
remove xs' g = case popFirst xs' of
    Nothing -> Nothing
    Just ((i,x),Nil) -> Just ((x,insertAvoidZero (i-1) x Nil), g)
    Just (v,xs) -> case randomR (0,fst v + totWeight xs - 1) g of
        (q,g')
          | q < fst v -> Just ((snd v,insertAvoidZero (fst v - 1) (snd v) xs),g')
          | otherwise -> case replace v xs g' of
            (((i,x),xs'),g'') -> Just ((x, insertAvoidZero (i-1) x xs'), g'')
  where            
    popFirst xs = case popFirst' xs of
        Just (Tree i (Leaf y),ys) -> Just ((i,y),ys)
        Nothing -> Nothing
        
    popFirst' Nil = Nothing
    popFirst' (Urn 0 x Nil) = Just (x, Nil)
    popFirst' (Urn 0 x (Urn i y ys)) = Just  (x, Urn (i+1) y ys)
    popFirst' (Urn i x xs) = case popFirst' (Urn (i-1) x xs) of
      Just (Tree j (Branch y z), ys) -> Just (y, Urn 0 (Tree (j - weight y) z) ys)
      
    insertAvoidZero :: Word -> a -> Urn a -> Urn a
    insertAvoidZero 0 _ x = x
    insertAvoidZero i x xs = insert i x xs
    
    replace v (Urn i x' xs') = go (\t -> Urn i t xs') id xs' (weight x' - 1) x'
      where
        go c _ Nil i x g = case treeReplace v x g of
            ((v',t'),g') -> ((v', c t'), g')
        go c k (Urn o x xs) j y g = case randomR (0,w) g of
            (q,g')
              | q < i     -> go (\t -> k (Urn o t xs))  (k . Urn o x) xs w x g'
              | otherwise -> go c (k . Urn o x) xs w y g'
          where
            i = weight x
            w = i + j
            
    treeReplace (i,v) (Tree w (Leaf x)) g = (((w,x),Tree i (Leaf v)), g)
    treeReplace v (Tree w (Branch xs ys)) g = case randomR (0,w-1) g of
        (q,g')
          | q < weight xs -> case treeReplace v xs g of
              ((v',t'),g'') -> ((v',Tree (w + (weight t' - weight xs)) (Branch t' ys)),g'')
          | otherwise -> case treeReplace v (Tree (w - weight xs) ys) g of
              ((v',t'),g'') -> ((v',Tree (weight xs + weight t') (Branch xs (branch t'))),g'')

    totWeight = go 0
      where
        go !i Nil = i
        go !i (Urn j _ xs) = go (i+j) xs
```

Merge is the same as on binomial heaps:

```haskell
merge :: Urn a -> Urn a -> Urn a
merge Nil ys = ys
merge xs Nil = xs
merge (Urn i x xs) (Urn j y ys) = merge' i x xs j y ys 
  where
    merge' i x xs j y ys = case compare i j of
        LT -> Urn i x (mergel xs (j-i-1) y ys)
        GT -> Urn j y (merger (i-j-1) x xs ys)
        EQ -> merge'' (succ i) (mergeTree x y) xs ys
    mergel Nil j y ys = Urn j y ys
    mergel (Urn i x xs) j y ys = merge' i x xs j y ys
    
    merger i x xs Nil = Urn i x xs
    merger i x xs (Urn j y ys) = merge' i x xs j y ys
    
    merge'' !i !t Nil ys = carryLonger i t ys
    merge'' !i !t xs Nil = carryLonger i t xs
    
    merge'' !p !t (Urn 0 x xs) (Urn 0 y ys) = Urn p t (merge'' 0 (mergeTree x y) xs ys)
    merge'' !p !t (Urn 0 x xs) (Urn j y ys) = merge'' (p+1) (mergeTree t x) xs (Urn (j-1) y ys)
    merge'' !p !t (Urn i x xs) (Urn 0 y ys) = merge'' (p+1) (mergeTree t y) (Urn (i-1) x xs) ys
    merge'' !p !t (Urn i x xs) (Urn j y ys) = Urn p t (merge (Urn (i-1) x xs) (Urn (j-1) y ys))
    carryLonger i t Nil = Urn i t Nil
    carryLonger i t (Urn 0 y ys) = carryLonger (succ i) (mergeTree t y) ys
    carryLonger i t (Urn j y ys) = Urn i t (Urn (j-1) y ys)
```

# Uses and Further Work

The efficient `merge` is intriguing: it means that `Urn` could conceivably be
`Alternative`, `MonadPlus`, etc. I have yet to see a use for that, but it's
interesting nonetheless! I'm constantly looking for a way to express something
like Dijkstra's algorithm algebraicly, using the usual `Alternative`
combinators; I don't know if this is related.

The other interesting point is that, for this to be an instance of
`Applicative`, it would need some analogue for multiplication for the weights.
I'm not sure what that should be. Also, it's not obvious how to translate what
we have into a min-heap version.

Finally, it might be worth trying out different heaps (a pairing heap is very
similar in structure to this). Also, we could rearrange the weights so that
larger ones are higher in each tree: this might give a performance boost.
