---
title: Single-Pass Huffman Coding
tags: Haskell, folds
bibliography: One Pass Laziness.bib
---

While working on something else, I figured out a nice Haskell implementation of Huffman coding, and I thought I'd share it here. I'll go through a few techniques for transforming a multi-pass algorithm into a single-pass one first, and then I'll show how to use them for Huffman. If you just want to skip to the code, it's provided at the end [^code].

## Circular Programming

There are several techniques for turning multi-pass algorithms into single-pass ones in functional languages. Perhaps the most famous is circular programming: using *laziness* to eliminate a pass. @bird_using_1984 used this to great effect in solving the repmin problem:

> Given a tree of integers, replace every integer with the minimum integer in the tree, in one pass.

For an imperative programmer, the problem is relatively easy: first, write the code to find the minimum value in the tree in the standard way, using a loop and a "smallest so far" accumulator. Then, inside the loop, after updating the accumulator, set the value of the leaf to be a *reference* to the accumulator.

At first, that solution may seem necessarily impure: we're using global, mutable state to update many things at once. However, as the paper shows, we can claw back purity using laziness:

```haskell
data Tree a = Leaf a | Tree a :*: Tree a

repMin :: Tree Integer -> Tree Integer
repMin xs = ys where
  (m, ys) = go xs
  go (Leaf x) = (x, Leaf m)
  go (xs :*: ys) = (min x y, xs' :*: ys')
    where
      (x,xs') = go xs
      (y,ys') = go ys
```

## There and Back Again

Let's say we don't have laziness at our disposal: are we hosed? No [^laziness]! @danvy_there_2005 explore this very issue, by posing the question:

> Given two lists, xs and ys, can you zip xs with the reverse of ys in one pass?

The technique used to solve the problem is named "There and Back Again"; it should be clear why from one of the solutions:

```haskell
convolve xs ys = walk xs const where
  walk [] k = k [] ys
  walk (x:xs) k = walk xs (\r (y:ys) -> k ((x,y) : r) ys)
```

The traversal of one list builds up the function to consume the other. We could write repmin in the same way:

```haskell
repMin = uncurry ($) . go where
  go (Leaf x) = (Leaf, x)
  go (xs :*: ys) = (\m -> xs' m :*: ys' m, min xm ym) where
    (xs',xm) = go xs
    (ys',ym) = go ys
```

[^laziness]: Well, that's a little bit of a lie. In terms of asympostics, @pippenger_pure_1997 stated a problem that could be solved in linear time in impure Lisp, but $\Omega(n \log n)$ in pure Lisp. @bird_more_1997 then produced an algorithm that could solve the problem in linear time, by using laziness. So, in some cases, laziness will give you asymptotics you can't get without it (if you want to stay pure).

## Cayley Representations

If you're doing a lot of appending to some list-like structure, you probably don't want to use actual lists: you'll end up traversing the left-hand-side of the append many more times than necessary. A type you can drop in to use instead is difference lists [@hughes_novel_1986]:

```haskell
type DList a = [a] -> [a]

rep :: [a] -> DList a
rep = (++)

abs :: DList a -> [a]
abs xs = xs []

append :: DList a -> DList a -> DList a
append = (.)
```

`append`{.haskell} is $\mathcal{O}(1)$ in this representation. In fact, for any monoid with a slow `mappend`{.haskell}, you can use the same trick: it's called the Cayley representation, and available as `Endo`{.haskell} in [Data.Monoid](https://hackage.haskell.org/package/base-4.10.1.0/docs/Data-Monoid.html#t:Endo).

```haskell
rep :: Monoid a => a -> Endo a
rep x = Endo (mappend x)

abs :: Monoid a => Endo a -> a
abs (Endo f) = f mempty

instance Monoid (Endo a) where
  mempty = Endo id
  mappend (Endo f) (Endo g) = Enfo (f . g)
```

You can actually do the same transformation for "monoids" in the categorical sense: applying it to monads, for instance, will give you codensity [@rivas_notions_2014].

## Traversable

Looking back—just for a second—to the repmin example, we should be able to spot a pattern we can generalize. There's really nothing tree-specific about it, so why can't we apply it to lists? Or other structures, for that matter? It turns out we can: the `mapAccumL`{.haskell} function is tailor-made to this need:

```haskell
repMin :: Traversable t => t Integer -> t Integer
repMin xs = ys where
  (~(Just m), ys) = mapAccumL f Nothing xs
  f Nothing x = (Just x, m)
  f (Just y) x = (Just (min x y), m)
```

The tilde before the `Just`{.haskell} ensures this won't fail on empty input.

# Huffman Coding

Finally, it's time for the main event. Huffman coding is a _very_ multi-pass algorithm, usually. The steps look like this:

1. Build a frequency table for each character in the input.
2. Build a priority queue from that frequency table.
3. Iteratively pop elements and combine them (into Huffman trees) from the queue until there's only one left.
4. That Huffman tree can be used to construct the mapping from items back to their Huffman codes.
5. Traverse the input again, using the constructed mapping to replace elements with their codes.

We can't *skip* any of these steps: we can try perform them all at once, though.

Let's write the multi-pass version first. We'll need the frequency table:

```haskell
frequencies :: Ord a => [a] -> Map a Int
frequencies = Map.fromListWith (+) . map (flip (,) 1)
```

And a heap, ordered on the frequencies of its elements (I'm using a skew heap here):

```haskell
data Heap a
  = Nil
  | Node {-# UNPACK #-} !Int a (Heap a) (Heap a)

instance Monoid (Heap a) where
  mappend Nil ys = ys
  mappend xs Nil = xs
  mappend h1@(Node i x lx rx) h2@(Node j y ly ry)
    | i <= j    = Node i x (mappend h2 rx) lx
    | otherwise = Node j y (mappend h1 ry) ly
  mempty = Nil
```

Next, we need to build the tree[^state]. We can use the tree type from above. 

[^state]: There's actually a nicer version of the `buildTree`{.haskell} function which uses `StateT (Heap a) Maybe`{.haskell}, but it's equivalent to this one under the hood, and I though might be a little distracting.

```haskell
buildTree :: Map a Int -> Maybe (Tree a)
buildTree = prune . toHeap where
  toHeap = Map.foldMapWithKey (\k v -> Node v (Leaf k) Nil Nil)
  prune Nil = Nothing
  prune (Node i x l r) = case mappend l r of
    Nil -> Just x
    Node j y l' r' ->
      prune (mappend (Node (i+j) (x :*: y) Nil Nil) (mappend l' r'))
```

Then, a way to convert between the tree and a map:

```haskell
toMapping :: Ord a => Tree a -> Map a [Bool]
toMapping (Leaf x) = Map.singleton x []
toMapping (xs :*: ys) =
    Map.union (fmap (True:) (toMapping xs)) (fmap (False:) (toMapping ys))
```

And finally, putting the whole thing together:

```haskell
huffman :: Ord a => [a] -> (Maybe (Tree a), [[Bool]])
huffman xs = (tree, map (mapb Map.!) xs) where
  freq = frequencies xs
  tree = buildTree freq
  mapb = maybe Map.empty toMapping tree
```

## Removing the passes

The first thing to fix is the `toMapping`{.haskell} function: at every level, it calls `union`{.haskell}, a complex and expensive operation. However, `union`{.haskell} and `empty`{.haskell} form a monoid, so we can use the Cayley representation to reduce the calls to a minimum. Next, we want to get rid of the `fmap`{.haskell}s: we can do that by assembling a function to perform the `fmap`{.haskell} as we go, as in `convolve`{.haskell}[^sharing].

```haskell
toMapping :: Ord a => Tree a -> Map a [Bool]
toMapping tree = go tree id Map.empty where
  go (Leaf x) k = Map.insert x (k [])
  go (xs :*: ys) k =
    go xs (k . (:) True) . go ys (k . (:) False)
```

[^sharing]: Something to notice about this function is that it's going top-down and bottom-up at the same time. Combining the maps (with `(.)`{.haskell}) is done bottom-up, but building the codes is top-down. This means the codes are built in reverse order! That's why the accumulating parameter (`k`{.haskell}) is a difference list, rather than a normal list. As it happens, if normal lists were used, the function would be slightly more efficient through sharing, but the codes would all be reversed.

Secondly, we can integrate the `toMapping`{.haskell} function with the `buildTree`{.haskell} function, removing another pass:

```haskell
buildTree :: Ord a => Map a Int -> Maybe (Tree a, Map a [Bool])
buildTree = prune . toHeap where
  toHeap = Map.foldMapWithKey (\k v -> Node v (Leaf k, leaf k) Nil Nil)
  prune Nil = Nothing
  prune (Node i x l r) = case mappend l r of
    Nil -> Just (fmap (\k -> k id Map.empty) x)
    Node j y l' r' ->
      prune (mappend (Node (i+j) (cmb x y) Nil Nil) (mappend l' r'))
  leaf x k = Map.insert x (k [])
  node xs ys k = xs (k . (:) True) . ys (k . (:) False)
  cmb (xt,xm) (yt,ym) = (xt :*: yt, node xm ym)
```

Finally, to remove the second pass over the list, we can copy repmin, using `mapAccumL`{.haskell} to both construct the mapping and apply it to the structure in one go.

```haskell
huffman :: (Ord a, Traversable t) => t a -> (Maybe (Tree a), t [Bool])
huffman xs = (fmap fst tree, ys) where
  (freq,ys) = mapAccumL f Map.empty xs
  f fm x = (Map.insertWith (+) x 1 fm, mapb Map.! x)
  tree = buildTree freq
  mapb = maybe Map.empty snd tree
```

And that's it!

# Generalization

The similarity between the repmin function and the solution above is suggestive: is there a way to _encode_ this idea of making a multi-pass algorithm single-pass? Of course! We can use an applicative:

```haskell
data Circular a b c =
    Circular !a
             (b -> c)

instance Functor (Circular a b) where
    fmap f (Circular tally run) = Circular tally (f . run)

instance Monoid a =>
         Applicative (Circular a b) where
    pure x = Circular mempty (const x)
    Circular fl fr <*> Circular xl xr =
        Circular
            (mappend fl xl)
            (\r -> fr r (xr r))

liftHuffman
    :: Ord a
    => a -> Circular (Map a Int) (Map a [Bool]) [Bool]
liftHuffman x = Circular (Map.singleton x 1) (Map.! x)

runHuffman
    :: Ord a
    => Circular (Map a Int) (Map a [Bool]) r -> (Maybe (Tree a), r)
runHuffman (Circular smry run) =
    maybe (Nothing, run Map.empty) (Just *** run) (buildTree smry)

huffman
    :: (Ord a, Traversable t)
    => t a -> (Maybe (Tree a), t [Bool])
huffman = runHuffman . traverse liftHuffman
```

Thanks to it being an applicative, you can do all the fun lensy things with it:

```haskell
showBin :: [Bool] -> String
showBin = map (bool '0' '1')

>>> let liftBin = fmap showBin . liftHuffman
>>> (snd . runHuffman . (each.traverse) liftBin) ("abb", "cad", "c")
(["01","11","11"],["00","01","10"],["00"])
```

Bringing us back to the start, it can also let us solve repmin!

```haskell
liftRepMin :: a -> Circular (Option (Min a)) a a
liftRepMin x = Circular (pure (pure x)) id

runRepMin :: Circular (Option (Min a)) a b -> b
runRepMin (Circular m r) = r (case m of
  Option (Just (Min x)) -> x)

repMin :: (Ord a, Traversable t) => t a -> t a
repMin = runRepMin . traverse liftRepMin
```

# Related

So the `Circular`{.haskell} type is actually just the product of reader and writer, and is closely related to the [sort](https://github.com/treeowl/sort-traversable) type.

It's also related to the [`Prescient`{.haskell}](https://www.reddit.com/r/haskell/comments/7qwzn4/an_update_about_the_store_monad_and_state_comonad/) type, which I noticed after I'd written the above.

[^code]: Huffman coding single-pass implementation:

    ```haskell
    import           Data.Map.Strict  (Map)
    import qualified Data.Map.Strict  as Map
    import           Data.Traversable (mapAccumL)
    
    data Heap a
      = Nil
      | Node {-# UNPACK #-} !Int a (Heap a) (Heap a)
    
    instance Monoid (Heap a) where
      mappend Nil ys = ys
      mappend xs Nil = xs
      mappend h1@(Node i x lx rx) h2@(Node j y ly ry)
        | i <= j    = Node i x (mappend h2 rx) lx
        | otherwise = Node j y (mappend h1 ry) ly
      mempty = Nil
    
    data Tree a = Leaf a | Tree a :*: Tree a

    buildTree :: Ord a => Map a Int -> Maybe (Tree a, Map a [Bool])
    buildTree = prune . toHeap where
      toHeap = Map.foldMapWithKey (\k v -> Node v (Leaf k, leaf k) Nil Nil)
      prune Nil = Nothing
      prune (Node i x l r) = case mappend l r of
        Nil -> Just (fmap (\k -> k id Map.empty) x)
        Node j y l' r' ->
          prune (mappend (Node (i+j) (cmb x y) Nil Nil) (mappend l' r'))
      leaf x k = Map.insert x (k [])
      node xs ys k = xs (k . (:) True) . ys (k . (:) False)
      cmb (xt,xm) (yt,ym) = (xt :*: yt, node xm ym)

    huffman :: (Ord a, Traversable t) => t a -> (Maybe (Tree a), t [Bool])
    huffman xs = (fmap fst tree, ys) where
      (freq,ys) = mapAccumL f Map.empty xs
      f fm x = (Map.insertWith (+) x 1 fm, mapb Map.! x)
      tree = buildTree freq
      mapb = maybe Map.empty snd tree
    ```

# References
