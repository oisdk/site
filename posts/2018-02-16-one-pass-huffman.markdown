---
title: One-Pass Huffman Encoding
tags: Haskell, folds
bibliography: One Pass Laziness.bib
---

While working on something else, I figured out a nice Haskell implementation of Huffman coding, and I thought I'd share it here. The algorithm is one-pass: the data is frequency-counted, Huffman-coded, and spat back out in one go. I'll go through the general techniques for transforming a multi-pass algorithm into a one-pass one first, and then the Huffman algorithm itself. If you just want to skip to the code, it's provided at the end [^code].

## Circular Programming

There are several techniques for turning multi-pass algorithms into single-pass ones in functional languages. Perhaps the most famous is circular programming: using *laziness* to eliminate a pass. @bird_using_1984 used this to great effect in solving the repmin problem:

> Given a tree of integers, replace every integer with the minimum integer in the tree, in one pass

The solution is quite magic:

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

`m`{.haskell} is generated from the traversal, _and_ used during the traversal. Haskell's laziness makes this possible: and importantly, the `m`{.haskell} is only evaluated once.

## There and Back Again

In an imperative language, the repmin problem might be solved with mutation: have a "largest so far" variable, and simply set every leaf to be a reference to that variable. And at first glance, especially with the imperative solution in mind, the repmin problem might seem intractable in a pure language. However, as the solution above demonstrates, it's often possible to claw back the performance characteristics of imperative languages using a little laziness and cleverness.

Let's say we only have the latter at our disposal: we're working in a strict language, and we want to be pure. Are we hosed? No! The paper There and Back Again [@danvy_there_2005] explores this very issue. The question which serves as the hook for that paper is as follows:

> Given two lists, xs and ys, can you zip xs with the reverse of ys in one pass?

Similar to the problem above, at first it seems almost impossible. Again, though, it is doable. In fact, in the paper, several different versions are provided. This is my favorite:

```haskell
convolve xs ys = walk xs const where
  walk [] k = k [] ys
  walk (x:xs) k = walk xs (\r (y:ys) -> k ((x,y) : r) ys)
```

As you can see, it uses a continuation-passing style, building up a function to consume one list as it traverses the other.

## Changing The Interpretation

One handy way to avoid doing work in programming is to change the _interpretation_ of data so it looks as if the work is already done. Say, for instance, you wanted to transpose a matrix. One way to do it is to actually perform the work of walking over the structure and swapping all of the required entries. However, if you know that your matrices are only going to be consumed by indexing into them, you could instead just go to every place you index into the "transposed" matrix and swap the x and y (I couldn't find a good paper for this technique so I'd love to see one if someone had one).

For lists, the canonical way (in Haskell at least) to consume is through folds. So, instead of preprocessing our data structure we can just change the particular fold we use. For instance, "convolve" really wants to reverse `ys`{.haskell} before it looks at it: if we can rewrite its consumption of `ys`{.haskell} as a fold, though, than we can swap out `foldr`{.haskell} for `foldl`{.haskell} and it won't know the difference!

Here's what we would do if we wanted to zip `xs`{.haskell} and `ys`{.haskell} in the normal order using a fold[^partial]:

[^partial]: You probably wouldn't write that function, actually, because it's partial. It fails if `ys`{.haskell} is longer than `xs`{.haskell}. The convolution problem, as stated in the paper, is only defined on lists of equal length: with dependent types we might be able to put that invariant in its signature. For a lovely overview of how to do exactly that (for this exact function), check out [this](https://www.youtube.com/watch?v=u_OsUlwkmBQ) talk by Kenneth Foner.

```haskell
zip xs ys = foldr f (const []) ys xs where
  f y ys (x:xs) = (x,y) : ys xs
```

So if we just swap the call to `foldr`{.haskell} (and flip) we get the convolve function:

```haskell
convolve xs ys = foldl f (const []) ys xs where
  f ys y (x:xs) = (x,y) : ys xs
```

In fact, if you inline `foldl`{.haskell} in the above function, you'll get the `convolve`{.haskell} from above.

## Traversable

Looking back—just for a second—to the repmin example, we should be able to spot a pattern we can generalize. There's really nothing tree-specific about it, so why can't we apply it to lists? Or other structures, for that matter? It turns out we can: the `mapAccumL`{.haskell} function is tailor-made to this need:

```haskell
repMin :: Traversable t => t Integer -> t Integer
repMin xs = ys where
  (~(Just m), ys) = mapAccumL f Nothing xs
  f Nothing x = (Just x, m)
  f (Just y) x = (Just (min x y), m)
```

The tilde before the just ensures this won't fail on empty input.

# Huffman Coding

Finally, it's time for the main event. Huffman coding is a _very_ multi-pass algorithm, usually. The steps look like this:

1. Build a frequency table for each character in the input.
2. Build a priority queue from that frequency table.
3. Iteratively pop elements and combine them (into Huffman trees) from the queue until there's only one left.
4. That Huffman tree can be used to construct the mapping from items back to their Huffman codes.
5. Traverse the input again, using the constructed mapping to replace elements wit their codes.

Now, in the "one-pass" version, we can't skip these steps: I just want to only walk over every data structure once.

For the multi-pass version, this is what we'll need. First, a frequency table:

```haskell
frequencies :: Ord a => [a] -> Map a Int
frequencies = Map.fromListWith (+) . map (flip (,) 1)
```

Then, a heap, ordered on the frequencies of its elements (I'm using a skew heap here):

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

The first thing to fix is the `toMapping`{.haskell} function: it's doing 2 `fmap`s of the map at _every_ level. We can remove them by passing in a continuation, as in `convolve`{.haskell}:

```haskell
toMapping :: Ord a => Tree a -> Map a [Bool]
toMapping tree = go tree id where
  go (Leaf x) k = Map.singleton x (k [])
  go (xs :*: ys) k =
    Map.union (go xs (k . (:) True)) (go ys (k . (:) False))
```

Secondly, we can integrate the `toMapping`{.haskell} function with the `buildTree`{.haskell} function, removing another pass:

```haskell
buildTree :: Ord a => Map a Int -> Maybe (Tree a, Map a [Bool])
buildTree = prune . toHeap where
  toHeap = Map.foldMapWithKey (\k v -> Node v (Leaf k, leaf k) Nil Nil)
  prune Nil = Nothing
  prune (Node i x l r) = case mappend l r of
    Nil -> Just (fmap ($id) x)
    Node j y l' r' ->
      prune (mappend (Node (i+j) (cmb x y) Nil Nil) (mappend l' r'))
  leaf x k = Map.singleton x (k [])
  node xs ys k = Map.union (xs (k . (:) True)) (ys (k . (:) False))
  cmb (xt,xm) (yt,ym) = (xt :*: yt, node xm ym)
```

Finally, to remove the second pass over the list, we can notice that second pass is using a result from the first computation (the mapping to huffman codes), and use the same trick as repmin. We'll construct the frequency table as we fill in the Huffman codes:

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

So what's the use of this? Well, for a start, it's lensy:

```haskell
showBin :: [Bool] -> String
showBin = map (bool '0' '1')

>>> let liftBin = fmap showBin . liftHuffman
>>> (snd . runHuffman . (each.traverse) liftBin) ("abb", "cad", "c")
(["01","11","11"],["00","01","10"],["00"])
```

And secondly, we can use it with repmin:

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

[^code]: Huffman coding one-pass implementation:

    ```haskell
    import           Data.Traversable (mapAccumL)
    import           Data.Map.Strict (Map)
    import qualified Data.Map.Strict as Map
    
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
        Nil -> Just (fmap ($id) x)
        Node j y l' r' ->
          prune (mappend (Node (i+j) (cmb x y) Nil Nil) (mappend l' r'))
      leaf x k = Map.singleton x (k [])
      node xs ys k = Map.union (xs (k . (:) True)) (ys (k . (:) False))
      cmb (xt,xm) (yt,ym) = (xt :*: yt, node xm ym)
    
    huffman :: (Ord a, Traversable t) => t a -> (Maybe (Tree a), t [Bool])
    huffman xs = (fmap fst tree, ys) where
      (freq,ys) = mapAccumL f Map.empty xs
      f fm x = (Map.insertWith (+) x 1 fm, mapb Map.! x)
      tree = buildTree freq
      mapb = maybe Map.empty snd tree
    ```

# References
