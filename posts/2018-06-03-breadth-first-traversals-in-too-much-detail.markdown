---
title: "Breadth-First Traversals in Far Too Much Detail"
tags: Haskell, Trees
series: Breadth-First Traversals
bibliography: Rose Tree Traversals.bib
---

After looking at the algorithms I [posted last time](2018-06-01-rose-trees-breadth-first-traversing.html), I noticed some patterns emerging which I thought deserved a slightly longer post. I'll go through the problem [@gibbons_breadth-first_2015] in a little more detail, and present some more algorithms to go along with it.

# The Problem

The original question was posed by [Etian Chatav](https://www.facebook.com/groups/programming.haskell/permalink/985981691412832/):

> What is the correct way to write breadth first traversal of a `[Tree]`{.haskell}?

The breadth-first traversal here is a traversal in the lensy sense, i.e:

```haskell
breadthFirst :: Applicative f => (a -> f b) -> [Tree a] -> f [Tree b]
```

The `Tree`{.haskell} type we're referring to here is a rose tree; we can take the one defined in [`Data.Tree`{.haskell}](http://hackage.haskell.org/package/containers-0.5.11.0/docs/Data-Tree.html#t:Tree):

```haskell
data Tree a
    = Node
    { rootLabel :: a
    , subForest :: [Tree a]
    }
```

Finally, instead of solving the (somewhat intermediate) problem of traversing a forest, we'll look directly at traversing the tree itself. In other words, our solution should have the type:

```haskell
breadthFirst :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
```

# Breadth-First Enumeration

As in @gibbons_breadth-first_2015, let's first look at just converting the tree to a list in breadth-first order. In other words, given the tree:

```
   ┌3
 ┌2┤
 │ └4
1┤
 │ ┌6
 └5┤
   └7
```

We want the list:

```haskell
[1,2,5,3,4,6,7]
```

Last time I looked at this problem, the function I arrived at was as follows:

```haskell
breadthFirstEnumerate :: Tree a -> [a]
breadthFirstEnumerate ts = f ts b []
  where
    f (Node x xs) fw bw = x : fw (xs : bw)

    b [] = []
    b qs = foldl (foldr f) b qs []
```

It's admittedly a little difficult to understand, but it's really not too complex: we're popping items off the front of a queue, and pushing the subforest onto the end. `fw`{.haskell} is the recursive call here: that's where we send the queue with the element pushed on. Even though it may *look* like we're pushing onto the front (as we're using a cons), this is really the *end* of the queue, since it's being consumed in reverse, with `foldl`{.haskell}.

This is similar to the technique used in @allison_circular_2006 and @smith_lloyd_2009, except we avoid explicitly tracking the length.

# Level-Order Enumeration

Before we go the full way to traversal, we can try add a little structure to our breadth-first enumeration, by delimiting between levels in the tree. We want our function to have the following type:

```haskell
levels :: Tree a -> [[a]]
```

Looking back at our example tree:

```
   ┌3
 ┌2┤
 │ └4
1┤
 │ ┌6
 └5┤
   └7
```

We now want the list:

```haskell
[[1],[2,5],[3,4,6,7]]
```

This function is strictly more powerful than `breadthFirstEnumerate`{.haskell}, as we can define one in terms of the other:

```haskell
breadthFirstEnumerate = concat . levels
```

It's also just a generally useful function, so there are several example implementations available online.

### Iterative-Style

The one provided in [Data.Tree](http://hackage.haskell.org/package/containers-0.5.11.0/docs/src/Data.Tree.html#levels) is as follows:

```haskell
levels t =
    map (map rootLabel) $
        takeWhile (not . null) $
        iterate (concatMap subForest) [t]
```

Pretty nice, but it looks to me like it's doing a lot of redundant work. We could write it as an unfold:

```haskell
levels t =  unfoldr (f . concat) [[t]]
  where
    f [] = Nothing
    f xs = Just (unzip [(y,ys) | Node y ys <- xs])
```

The performance danger here lies in `unzip`{.haskell}: one could potentially optimize that for a speedup.

### With an (implicit) Queue

Another definition, in the style of `breadthFirstEnumerate`{.haskell} above, is as follows:

```haskell
levels ts = f b ts [] []
  where
    f k (Node x xs) ls qs = k (x : ls) (xs : qs)

    b _ [] = []
    b k qs = k : foldl (foldl f) b qs [] []
```

Here, we maintain a stack building up the current level, as well as a queue that we send to the next level. Because we're consing onto the front of the stack, the subforest needs to be traversed in reverse, to build up the output list in the right order. This is why we're using a second `foldl`{.haskell} here, whereas the original had `foldr`{.haskell} on the inner loop.

### Zippy-Style

Looking at the implicit queue version, I noticed that it's just using a church-encoded pair to reverse the direction of the fold. Instead of doing both reversals, we can use a normal pair, and run it in one direction:

```haskell
levels ts = b (f ts ([],[]))
  where
    f (Node x xs) (ls,qs) = (x:ls,xs:qs)

    b (_,[]) = []
    b (k,qs) = k : b (foldr (flip (foldr f)) ([],[]) qs)
```

Secondly, we're running a fold on the second component of the pair: why not run the fold immediately, rather than building the intermediate list. In fact, we're running a fold over the *whole* thing, which we can do straight away:

```haskell
levels ts = f ts []
  where
    f (Node x xs) (q:qs) = (x:q) : foldr f qs xs
    f (Node x xs) []     = [x]   : foldr f [] xs
```

After looking at it for a while, I realized it's similar to an inlined version of the algorithm presented in @gibbons_breadth-first_2015:

```haskell
levels t = [rootLabel t] : foldr (lzw (++)) [] (map levels (subForest t))
  where
    lzw f (x:xs) (y:ys) = f x y : lzw f xs ys
    lzw _ xs [] = xs
    lzw _ [] ys = ys
```

# Cofree

Before going any further, all of the functions so far can be redefined to work on the [cofree comonad](http://hackage.haskell.org/package/free-5.0.2/docs/Control-Comonad-Cofree.html):

```haskell
data Cofree f a = a :< f (Cofree f a)
```

When `f`{.haskell} is specialized to `[]`{.haskell}, we get the original rose tree. So far, though, all we actually require is `Foldable`{.haskell}.

From now on, then, we'll use `Cofree`{.haskell} instead of `Tree`{.haskell}.

# Traversing

Finally, we can begin on the traversal itself. We know how to execute the effects in the right order, what's missing is to build the tree back up in the right order.

### Filling

First thing we'll use is a trick with `Traversable`{.haskell}, where we fill a container from a list. In other words:

```haskell
fill [(),(),(),()] [1..] = ([1,2,3,4],[5..])
```

With the state monad (or applicative, in this case, I suppose), we can define a "pop" action, which takes an element from the supply:

```haskell
pop = state (\(x:xs) -> (x,xs))
```

And then we `traverse`{.haskell} that action over our container:

```haskell
fill = traverse (const pop)
```

When we use fill, it'll have the following type:

```haskell
breadthFirst :: (Applicative f, Traversable t)
             => (a -> f b) -> Cofree t a -> f (Cofree t b)
breadthFirst = ...
  where
    ...
    fill :: t (Cofree t a) -> State [Cofree t b] (t (Cofree t b))
    fill = traverse (const pop)
```

Hopefully that makes sense: we're going to get the subforest from here:

```haskell
data Cofree t a = a :< t (Cofree t a)
                       ^^^^^^^^^^^^^^
```

And we're going to fill it with the result of the traversal, which changes the contents from `a`s to `b`s.

### Composing Applicatives

One of the nice things about working with applicatives is that they compose, in a variety of different ways. In other words, if I have one effect, `f`{.haskell}, and another `g`{.haskell}, and I want to run them both on the contents of some list, I can do it in one pass, either by layering the effects, or putting them side-by-side.

In our case, we need to deal with two effects: the one generated by the traversal, (the one the caller wants to use), and the internal state we're using to fill up the forests in our tree. We could use [`Compose`{.haskell}](http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Functor-Compose.html#t:Compose) explicitly, but we can avoid some calls to `pure`{.haskell} if we write the combinators we're going to use directly:

```haskell
map2
    :: (Functor f, Functor g)
    => (a -> b -> c) -> f a -> g b -> f (g c)
map2 f x xs =
    fmap (\y -> fmap (f y) xs) x

app2
    :: (Applicative f, Applicative g)
    => (a -> b -> c -> d) -> f a -> g b -> f (g c) -> f (g d)
app2 f x xs =
    liftA2 (\y -> liftA2 (f y) xs) x
```

The outer applicative (`f`) will be the user's effect, the inner will be `State`.

# Take 1: Zippy-Style Traversing

First we'll try convert the zippy-style `levels`{.haskell} to a traversal. First, convert the function over to the cofree comonad:

```haskell
levels tr = f tr []
  where
    f (x:<xs) (q:qs) = (x:q) : foldr f qs xs
    f (x:<xs) []     = [x]   : foldr f [] xs
```

Next, instead of building up a list of just the root labels, we'll pair them with the subforests:

```haskell
breadthFirst tr = f tr []
  where
    f (x:<xs) (q:qs) = ((x,xs):q) : foldr f qs xs
    f (x:<xs) []     = [(x,xs)]   : foldr f [] xs
```

Next, we'll fill the subforests:

```haskell
breadthFirst tr = f tr []
  where
    f (x:<xs) (q:qs) = ((x,fill xs):q) : foldr f qs xs
    f (x:<xs) []     = [(x,fill xs)]   : foldr f [] xs
```

Then, we can run the applicative effect on the root label:

```haskell
breadthFirst c tr = f tr []
  where
    f (x:<xs) (q:qs) = ((c x,fill xs):q) : foldr f qs xs
    f (x:<xs) []     = [(c x,fill xs)]   : foldr f [] xs
```

Now, to combine the effects, we can use the combinators we defined before:

```haskell
breadthFirst c tr = f tr []
  where
    f (x:<xs) (q:qs) =
        app2 (\y ys zs -> (y:<ys) : zs) (c x) (fill xs) q : foldr f qs xs
    f (x:<xs) [] =
        map2 (\y ys -> [y:<ys]) (c x) (fill xs) : foldr f [] xs
```

This builds a list containing all of the level-wise traversals of the tree. To collapse them into one, we can use a fold:

```haskell
breadthFirst :: (Traversable t, Applicative f)
             => (a -> f b)
             -> Cofree t a
             -> f (Cofree t b)
breadthFirst c tr =
    head <$> foldr (liftA2 evalState) (pure []) (f tr [])
  where
    f (x:<xs) (q:qs) =
        app2 (\y ys zs -> (y:<ys):zs) (c x) (fill xs) q : foldr f qs xs
    f (x:<xs) [] =
        map2 (\y ys -> [y:<ys]) (c x) (fill xs) : foldr f [] xs
```

# Take 2: Queue-Based Traversing

Converting the queue-based implementation is easy once we've done it with the zippy one. The result is (to my eye) a little easier to read, also:

```haskell
breadthFirst
    :: (Applicative f, Traversable t)
    => (a -> f b) -> Cofree t a -> f (Cofree t b)
breadthFirst c tr =
    fmap head (f b tr e [])
  where
    f k (x:<xs) ls qs =
      k (app2 (\y ys zs -> (y:<ys):zs) (c x) (fill xs) ls) (xs:qs)

    b _ [] = pure []
    b l qs = liftA2 evalState l (foldl (foldl f) b qs e [])

    e = pure (pure [])
```

There are a couple things to notice here: first, we're not using `map2`{.haskell} anywhere. That's because in the zippy version we were able to notice when the queue was exhausted, so we could just output the singleton effect. Here, instead, we're using `pure (pure [])`{.haskell}: this is potentially a source of inefficiency, as `liftA2 f (pure x) y`{.haskell} is less efficient than `fmap (f x) y`{.haskell} for some applicatives.

On the other hand, we don't build up a list of levels to be combined with `foldr (liftA2 evalState)`{.haskell} at any point: we combine them at every level immediately. You may be able to do the same in the zippy version, but I haven't figured it out yet.

### Yoneda

The final point to make here is to do with the very last thing we do in the traversal: `fmap head`{.haskell}. Strictly speaking, any `fmap`{.haskell}s in the code should be unnecessary: we *should* be able to fuse them all with any call to `liftA2`{.haskell}. This transformation is often called the "Yoneda embedding". We can use it here like so:

```haskell
breadthFirst
    :: ∀ t a f b. (Traversable t, Applicative f)
    => (a -> f b) -> Cofree t a -> f (Cofree t b)
breadthFirst c tr = f (b head) tr e []
  where
    f k (x:<xs) ls qs =
        k (app2 (\y ys zs -> (y:<ys) : zs) (c x) (fill xs) ls) (xs : qs)

    b :: ∀ x. ([Cofree t b] -> x)
      -> f (State [Cofree t b] [Cofree t b])
      -> [t (Cofree t a)]
      -> f x
    b k _ [] = pure (k [])
    b k l qs =
        liftA2 (\x -> k . evalState x) l (foldl (foldl f) (b id) qs e [])

    e = pure (pure [])
```

Notice that we need scoped type variables here, since the type of `b`{.haskell} changes depending on when it's called.

# Take 3: Iterative Traversing

Transforming the iterative version is slightly different from the other two:

```haskell
breadthFirst c tr = fmap head (go [tr])
  where
    go [] = pure []
    go xs =
        liftA2
            evalState
            (getCompose (traverse f xs))
            (go (foldr (\(_:<ys) b -> foldr (:) b ys) [] xs))
    f (x:<xs) = Compose (map2 (:<) (c x) (fill xs))
```

We're using `Compose`{.haskell} directly here, in contrast to the other two algorithms.

# Comparison

Performance-wise, no one algorithm wins out in every case. For enumeration, the zippy algorithm is the fastest in most cases---except when the tree had a large branching factor; then, the iterative algorithm wins out. For the traversals, the iterative algorithm is usually better---except for monads with more expensive applicative instances.

I'm still not convinced that the zippy traversal is as optimized as it could be, however. If anyone has a better implementation, I'd love to see it!

# Fusion

Using the composability of applicatives, we can fuse several operations over traversables into one pass. Unfortunately, however, this can often introduce a memory overhead that makes the whole operation slower overall. One such example is the iterative algorithm above:

```haskell
breadthFirst c tr = fmap head (go [tr])
  where
    go [] = pure []
    go xs = liftA2 evalState zs (go (ys []))
      where
        Compose (Endo ys,Compose zs) = traverse f xs
    f (x :< xs) =
        Compose
            (Endo (flip (foldr (:)) xs)
            ,Compose (map2 (:<) (c x) (fill xs)))
```

We only traverse the subforest of each node once now, fusing the fill operation with building the list to send to the recursive call. This is expensive (especially memory-wise), though, and traversing the descendant is cheap; the result is that the one-pass version is slower (in my tests).

# Generalizing

The cofree comonad allows us to generalize over the type of "descendants"---from lists (in `Tree`{.haskell}) to anything traversable. We could also generalize over the type of the traversal itself: given a way to access the descendants of a node, we should be able to traverse all nodes in a breadth-first order. This kind of thing is usually accomplished by [Plated](http://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-Plated.html): it's a class that gives you a traversal over the immediate descendants of some recursive type. Adapting the iterative version is relatively simple:

```haskell
breadthFirstOf :: Traversal' a a -> Traversal' a a
breadthFirstOf trav c tr = fmap head (go [tr])
  where
    go [] = pure []
    go xs =
        liftA2
            evalState
            (getCompose (traverse f xs))
            (go (foldr (\ys b -> foldrOf trav (:) b ys) [] xs))
    f xs = Compose (fmap fill (c xs))
    fill = trav (const (State (\(x:xs) -> (x, xs))))
```

We can use this version to get back some of the old functions above:

```haskell
breadthFirstEnumerate ::  Traversable f => Cofree f a -> [a]
breadthFirstEnumerate = toListOf (breadthFirstOf plate . _extract)
```

# Unfolding

Building a tree breadth-first, monadically, is still an unsolved problem [it looks like: @feuer_is_2015].

Using some of these we can implement a monadic breadth-first unfold for the cofree comonad:

```haskell
unfoldM :: (Monad m, Traversable t)
        => (b -> m (a, t b))
        -> b
        -> m (Cofree t a)
unfoldM c tr = go head [tr]
  where
    go k [] = pure (k [])
    go k xs = do
        ys <- traverse c xs
        go (k . evalState (traverse f ys)) (toList (Compose (Compose ys)))
    f (x,xs) = fmap (x:<) (fill xs)
```

# References
