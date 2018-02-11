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

[^new-filterm]: The definition has since been [updated](https://hackage.haskell.org/package/base-4.10.1.0/docs/src/Control.Monad.html#filterM) to more modern Haskell: it now uses a fold, and only requires `Applicative`{.haskell}.

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

So these monadic generalisations have been discovered before, several times over. There's even a [package](https://hackage.haskell.org/package/monadlist-0.0.2) with monadic versions of the functions in Data.List. Exploring this idea with a little more formality is the paper "All Sorts of Permutations" [@christiansen_all_2016], and accompanying presentation [on YouTube](https://www.youtube.com/watch?v=vV3jqTxJ9Wc). They show that the monadic version of sort produces permutations of the input list, and examine the output from different sorting algorithms. Here's a couple of their implementations, altered slightly:

```haskell
insertM :: Monad m => (a -> a -> m Bool) -> a -> [a] -> m [a]
insertM _ x [] = pure [x]
insertM p x yys@(y:ys) = do
  lte <- p x y
  if lte
    then pure (x:yys)
    else fmap (y:) (insertM p x ys)

insertSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
insertSortM p = foldrM (insertM p) []

partitionM :: Applicative m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM p = foldr f (pure ([],[])) where
  f x = liftA2 ifStmt (p x) where
    ifStmt flg (tr,fl)
      | flg = (x:tr,fl)
      | otherwise = (tr,x:fl)
      
quickSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
quickSortM p [] = pure []
quickSortM p (x:xs) = do
  (gt,le) <- partitionM (p x) xs
  ls <- quickSortM p le
  gs <- quickSortM p gt
  pure (ls ++ [x] ++ gs)

>>> insertSortM (\_ _ -> [False,True]) [1,2,3]
[[1,2,3],[1,3,2],[3,1,2],[2,1,3],[2,3,1],[3,2,1]]

>>> quickSortM (\_ _ -> [False,True]) [1,2,3]
[[3,2,1],[2,3,1],[2,1,3],[3,1,2],[1,3,2],[1,2,3]]
```

As it should be easy to see, they're very concise and elegant, and strongly resemble the pure versions of the algorithms.

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

One of the nicest things about the paper was the diagrams of decision trees provided for each sorting algorithm. I couldn't find a library to do that for me, so I had a go at producing my own. First, we'll need a data type to represent the tree itself:

```haskell
data DecTree t a
  = Pure a
  | Choice t (DecTree t a) (DecTree t a)
  deriving Functor
```

We'll say the left branch is "true" and the right "false". Applicative and monad instances are relatively mechanical[^free-dec]:

[^free-dec]: Part of the reason the instances are so mechanical is that this type strongly resembles the [free monad](https://hackage.haskell.org/package/free-5/docs/Control-Monad-Free.html#t:Free):

    `data Free f a = Pure a | Free (f (Free f a))`{.haskell}

    In fact, the example given in the `MonadFree`{.haskell} class is the following:

    `data Pair a = Pair a a`{.haskell}

    `type Tree = Free Pair`{.haskell}

    The only difference with the above type and the decision tree is that the decision tree carries a tag with it.

    So what's so interesting about this relationship? Well, `Pair`{.haskell} is actually a [representable functor](https://hackage.haskell.org/package/adjunctions-4.4/docs/Data-Functor-Rep.html). Any representable functor `f a`{.haskell} can be converted to (and from) a function `key -> a`{.haskell}, where `key`{.haskell} is the specific key for `f`{.haskell}. The key for `Pair`{.haskell} is `Bool`{.haskell}: the result of the function we passed in to the sorting functions!

    In general, you can make a "decision tree" for any function of type `a -> b`{.haskell} like so:

    `type DecTree a b r = Rep f ~ b => Free (Compose ((,) a) f) r`{.haskell}

    But more on that in a later post.

```haskell
instance Applicative (DecTree t) where
  pure = Pure
  Pure f <*> xs = fmap f xs
  Choice c ls rs <*> xs = Choice c (ls <*> xs) (rs <*> xs)
  
instance Monad (DecTree t) where
  Pure x >>= f = f x
  Choice c ls rs >>= f = Choice c (ls >>= f) (rs >>= f)
```

We can now create a comparator function that constructs one of these trees, and remembers the values it was given:

```haskell
traceCompare :: a -> a -> DecTree (a,a) Bool
traceCompare x y = Choice (x,y) (Pure True) (Pure False)
```

Finally, to draw the tree, I'll use a function from my [binary tree](https://github.com/oisdk/binary-tree) library:

```haskell
printDecTree :: (Show a, Show b) => String -> DecTree (a,a) b -> IO ()
printDecTree rel t = putStr (drawTreeWith id (go t) "") where
  go (Pure xs) = Node (show xs) Leaf Leaf
  go (Choice (x,y) tr fl) =
    Node (show x ++ rel ++ show y) (go tr) (go fl)
```

And we get these really nice diagrams out:

```haskell
>>> (printDecTree "<=" . insertSortM traceCompare) [1,2,3]

         ┌[1,2,3]
    ┌1<=2┤
    │    │    ┌[2,1,3]
    │    └1<=3┤
    │         └[2,3,1]
2<=3┤
    │    ┌[1,3,2]
    └1<=3┤
         │    ┌[3,1,2]
         └1<=2┤
              └[3,2,1]

>>> (printDecTree "<=" . quickSortM traceCompare) [1,2,3]

              ┌[1,2,3]
         ┌2<=3┤
         │    └[1,3,2]
    ┌1<=3┤
    │    └[3,1,2]
1<=2┤
    │    ┌[2,1,3]
    └1<=3┤
         │    ┌[2,3,1]
         └2<=3┤
              └[3,2,1]
```

We can also try it out with the other monadic list functions:

```haskell
>>> (printDecTree "=" . groupByM traceCompare) [1,2,3]

       ┌[[1,2,3]]
   ┌2=3┤
   │   └[[1,2],[3]]
1=2┤
   │   ┌[[1],[2,3]]
   └2=3┤
       └[[1],[2],[3]]
```

## Applicative

You might notice that none of these "monadic" functions actually require a monad constraint: they're all applicative. There's a straightforward implementation that relies only on applicative for most of these functions, with a notable exception: sort. Getting *that* to work with just applicative is the subject of a future post.

### References
