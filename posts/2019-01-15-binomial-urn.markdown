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

The first better fold I found was Jon Fairbairn's  simple `treeFold`:

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
priority queue under the hood, and how it exploited laziness to get sharing.

I've gotten huge mileage out of this fold and the general ideas about it, and
today I'm going to show one more use of it. We're going to improve some of the
asymptotics of the data structure presented in @lampropoulos_ode_2017.

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

# Priority Queues

The key thing to notice in the paper which will let us improve the structure is
that what they're designing is actually a *priority queue*. Well, a weird
looking priority queue, but a priority queue nonetheless.

Think about it like a max-priority queue (pop returns the largest element first), with a
degree of "randomization". In other words, when you go to do a pop, all of the
comparisons between the ordering keys (the weights in this case) sprinkles some
randomness into the equation, meaning that instead of `1 < 2` returning `True`,
it returns `True` $\frac{2}{3}$ of the time, and `False` the other
$\frac{1}{3}$.

This way of doing things means that not every priority queue is suitable: we want to run
comparisons at `pop` time (not `insert`), so a binary heap (for instance) won't
do. At branches (non-leaves), the queue will only be allowed store *summaries*
of the data, not the "max element".

The one presented in the paper is something like a Braun priority queue: the
$\mathcal{O}(n)$ `fromList` implementation is reminiscent of the one in
@okasaki_three_1997.

So what priority queue can we choose to get us the desired efficiency? Why, a binomial one
of course!

# The Data Structure

The urn structure itself looks a lot like a binomial heap:

```haskell
data Tree a
  = Tree
  { weight :: {-# UNPACK #-} !Word
  , branch :: Node a
  }
  
data Node a
  = Leaf a
  | Branch (Tree a) (Node a)

data Heap a
  = Nil
  | Cons {-# UNPACK #-} !Word (Tree a) (Heap a)
  
data Urn a
  = Urn
  { totWeight :: {-# UNPACK #-} !Word
  , heap      :: !(Heap a)
  }
```

By avoiding the usual `Skip` constructors you often see in a binomial heap we
save a huge amount of space. Instead, we store the "number of zeroes before this
bit". Another thing to point out is that only left branches in the trees store
their weight: the same optimization is made in the paper.

Insertion is not much different from insertion for a usual binomial priority queue,
although we don't need to do anything to merge the trees:

```haskell
insertHeap :: Word -> a -> Heap a -> Heap a
insertHeap i' x' = go 0 (Tree i' (Leaf x'))
  where
    go !i x Nil = Cons i x Nil
    go !i x (Cons 0 y ys) = go (i+1) (mergeTree x y) ys
    go !i x (Cons j y ys) = Cons i x (Cons (j-1) y ys)
    
insert :: Word -> a -> Urn a -> Urn a
insert i x (Urn w xs) = Urn (i+w) (insertHeap i x xs)

mergeTree :: Tree a -> Tree a -> Tree a
mergeTree xs ys =
    Tree
      (weight xs + weight ys)
      (Branch xs (branch ys))
```

We *could* potentially get insertion from amortized $\mathcal{O}(1)$ to
worst-case $\mathcal{O}(1)$ by using skew binary instead of binary (in fact I am
almost sure it's possible), but then I think we'd lose the efficient merge. I'll
leave exploring that for another day.

Sampling (with replacement) first randomly chooses a tree from the top-level
list, and then we drill down into that tree with binary search.

```haskell
sample :: RandomGen g => Urn a -> g -> Maybe (a, g)
sample (Urn _ Nil) = const Nothing
sample (Urn w' (Cons i' x' xs')) = Just . go (w' - 1) i' x' xs'
  where
    go w i x Nil g = go' (weight x - 1) (branch x) g
    go w i x (Cons j y ys) g = case randomR (0,w) g of
        (q,g')
          | q < weight x -> go' (weight x - 1) (branch x) g'
          | otherwise    -> go  (w - weight x) j y ys g'
    go' _ (Leaf x) g = (x, g)
    go' i (Branch xs ys) g = case randomR (0,i) g of
        (q,g')
          | q < weight xs -> go' (weight xs - 1) (branch xs) g'
          | otherwise     -> go' (i - weight xs) ys g'
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
remove (Urn w' xs') g = case popFirst xs' of
    Nothing -> Nothing
    Just (v@(Tree i (Leaf x)),Nil) -> Just ((x, Urn (w'-1) (insert' (i-1) x Nil)),g)
    Just (v@(Tree i (Leaf x)), xs@(Cons j y ys)) -> case randomR (0,w' - 1) g of
        (q,g')
          | q < i -> Just ((x,Urn (w'-1) (insert' (i-1) x xs)), g')
          | otherwise -> case replace i x j y ys g' of
              (((k,z),zs),g'') -> Just ((z, Urn (w'-1) (insert' (k-1) z zs)), g'')
  where        
    popFirst Nil = Nothing
    popFirst (Cons 0 x Nil) = Just (x, Nil)
    popFirst (Cons 0 x (Cons i y ys)) = Just  (x, Cons (i+1) y ys)
    popFirst (Cons i x xs) = case popFirst (Cons (i-1) x xs) of
      Just (Tree j (Branch y z), ys) -> Just (y, Cons 0 (Tree (j - weight y) z) ys)
      
    insert' 0 _ x = x
    insert' i x xs = insertHeap i x xs
    
    replace iv v i x' xs' = go (\t -> Cons i t xs') id xs' (weight x' - 1) x'
      where
        go c _ Nil i x g = case replaceTree iv v x g of
            ((v',t'),g') -> ((v', c t'), g')
        go c k (Cons o x xs) j y g = case randomR (0,w) g of
            (q,g')
              | q < weight x -> go (\t -> k (Cons o t xs))  (k . Cons o x) xs w x g'
              | otherwise    -> go c (k . Cons o x) xs w y g'
          where
            i = weight x
            w = i + j
            
    replaceTree iv v (Tree w (Leaf x)) g = (((w,x),Tree iv (Leaf v)), g)
    replaceTree iv v (Tree w (Branch xs ys)) g = case randomR (0,w-1) g of
        (q,g')
          | q < weight xs -> case replaceTree iv v xs g of
              ((v',t'),g'') -> ((v',Tree (w + (weight t' - weight xs)) (Branch t' ys)),g'')
          | otherwise -> case replaceTree iv v (Tree (w - weight xs) ys) g of
              ((v',t'),g'') -> ((v',Tree (weight xs + weight t') (Branch xs (branch t'))),g'')
```

Merge is the same as on binomial heaps:

```haskell
merge :: Urn a -> Urn a -> Urn a
merge (Urn i' xs') (Urn j' ys') = Urn (i'+j') (go xs' ys')
  where
    go Nil ys = ys
    go (Cons i x xs) ys = merger i x xs ys

    merge' i x xs j y ys = case compare i j of
        LT -> Cons i x (mergel xs (j-i-1) y ys)
        GT -> Cons j y (merger (i-j-1) x xs ys)
        EQ -> merge'' (succ i) (mergeTree x y) xs ys

    mergel Nil j y ys = Cons j y ys
    mergel (Cons i x xs) j y ys = merge' i x xs j y ys
    
    merger !i x xs Nil = Cons i x xs
    merger !i x xs (Cons j y ys) = merge' i x xs j y ys
    
    merge'' !i !t Nil ys = carryLonger i t ys
    merge'' !i !t xs Nil = carryLonger i t xs
    merge'' !p !t (Cons 0 x xs) (Cons 0 y ys) = Cons p t (merge'' 0 (mergeTree x y) xs ys)
    merge'' !p !t (Cons 0 x xs) (Cons j y ys) = merge'' (p+1) (mergeTree t x) xs (Cons (j-1) y ys)
    merge'' !p !t (Cons i x xs) (Cons 0 y ys) = merge'' (p+1) (mergeTree t y) (Cons (i-1) x xs) ys
    merge'' !p !t (Cons i x xs) (Cons j y ys) = Cons p t (go (Cons (i-1) x xs) (Cons (j-1) y ys))

    carryLonger !i t Nil = Cons i t Nil
    carryLonger !i t (Cons 0 y ys) = carryLonger (succ i) (mergeTree t y) ys
    carryLonger !i t (Cons j y ys) = Cons i t (Cons (j-1) y ys)    
```

# Uses and Further Work

First and foremost, I should test the above implementations! I'm pretty
confident the asymptotics are correct, but I am pretty sure the implementations
will have bugs.

The efficient `merge` is intriguing: it means that `Urn` could conceivably be
`Alternative`, `MonadPlus`, etc. I have yet to see a use for that, but it's
interesting nonetheless! I'm constantly looking for a way to express something
like Dijkstra's algorithm algebraicly, using the usual `Alternative`
combinators; I don't know if this is related.

The other interesting point is that, for this to be an instance of
`Applicative`, it would need some analogue for multiplication for the weights.
I'm not sure what that should be.

This is inherently *max*-priority. It's not obvious how to translate what we
have into a min-priority queue version.

Finally, it might be worth trying out different priority queues (a pairing
heap is very similar in structure to this). Also, we could rearrange the weights
so that larger ones are higher in each tree: this might give a performance
boost.
