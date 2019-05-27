---
title: Deriving a Linear-Time Applicative Traversal of a Rose Tree
series: Breadth-First Traversals
tags: Haskell
bibliography: Rose Tree Traversals.bib
---

# The Story so Far

Currently, we have several different ways to enumerate a tree in breadth-first
order.
The typical solution (which is the usual recommended approach in imperative
programming as well) uses a *queue*, as described by
@okasaki_breadth-first_2000.
If we take the simplest possible queue (a list), we get a quadratic-time
algorithm, with an albeit simple implementation.
The next simplest version is to use a banker's queue (which is just a pair of
lists).
From this version, if we inline and apply identities like the following:

```haskell
foldr f b . reverse = foldl (flip f) b
```

We'll get to the following definition:

```haskell
bfe :: Forest a -> [a]
bfe ts = foldr f b ts []
  where
    f (Node x xs) fw bw = x : fw (xs : bw)

    b [] = []
    b qs = foldl (foldr f) b qs []
```

We can get from this function to others (like one which uses a corecursive
queue, and so on) through a similar derivation.
I might some day write a post on each derivation, starting from the simple
version and demonstrating how to get to the more efficient at each step.

For today, though, I'm interested in the *traversal* of a rose tree.
Traversal, here, of course, is in the applicative sense.

Thus far, I've managed to write linear-time traversals, but they've been
unsatisfying.
They work by enumerating the tree, traversing the effectful function over the
list, and then rebuilding the tree.
Since each of those steps only takes linear time, the whole thing is indeed a
linear-time traversal, but I hadn't been able to fuse away the intermediate
step.

# Phases

The template for the algorithm I want comes from the `Phases` applicative
[@easterly_functions_2019]:

```haskell
data Phases f a where
  Lift   :: f a -> Phases f a
  (:<*>) :: f (a -> b) -> Phases f a -> Phases f b
```

We can use it to write a breadth-first traversal like so:

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (traverse go xs))
```

The key component that makes this work is that it combines applicative effects
in parallel:

```haskell
instance Functor f => Functor (Phases f) where
    fmap f (Lift x) = Lift (fmap f x)
    fmap f (fs :<*> xs) = fmap (f.) fs :<*> xs
    
instance Applicative f => Applicative (Phases f) where
    pure = Lift . pure
    Lift fs      <*> Lift xs      = Lift (fs <*> xs)
    (fs :<*> gs) <*> Lift xs      = liftA2 flip fs xs :<*> gs
    Lift fs      <*> (xs :<*> ys) = liftA2 (.)  fs xs :<*> ys
    (fs :<*> gs) <*> (xs :<*> ys) = liftA2 c    fs xs :<*> liftA2 (,) gs ys
      where
        c f g ~(x,y) = f x (g y)
```

We're also using the following helper functions:

```haskell
runPhases :: Applicative f => Phases f a -> f a
runPhases (Lift x) = x
runPhases (fs :<*> xs) = fs <*> runPhases xs

later :: Applicative f => Phases f a -> Phases f a
later = (:<*>) (pure id)
```

The problem is that it's quadratic: the `traverse` in:

```haskell
go (Node x xs) = liftA2 Node (Lift (f x)) (later (traverse go xs))
```

Hides some expensive calls to `<*>`.

# A Roadmap for Optimisation

The problem with the `Phases` traversal is actually analogous to another
function for enumeration: `levels` from @gibbons_breadth-first_2015.

```haskell
levels :: Tree a -> [[a]]
levels (Node x xs) = [x] : foldr lzw [] (map levels xs)
  where
    lzw [] ys = ys
    lzw xs [] = xs
    lzw (x:xs) (y:ys) = (x ++ y) : lzw xs ys
```

`lzw` takes the place of `<*>` here, but the overall issue is the same: we're
zipping at every point, making the whole thing quadratic.

However, from the above function we *can* derive a linear time enumeration.
It looks like this:

```haskell
levels :: Tree a -> [[a]]
levels ts = f ts []
  where
    f (Node x xs) (q:qs) = (x:q) : foldr f qs xs
    f (Node x xs) []     = [x]   : foldr f [] xs
```

Our objective is clear, then: try to derive the linear-time implementation of
`bft` from the quadratic, in a way analogous to the above two functions.
This is actually relatively straightforward once the target is clear: the rest
of this post is devoted to the derivation.

# Derivation

First, we start off with the original `bft`.

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (traverse go xs))
```

<details>
<summary>
Inline `traverse`.
</summary>

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (go' xs))
    go' = foldr (liftA2 (:) . go) (pure [])
```

</details>
<details>
<summary>
Factor out `go''`.
</summary>

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (go' xs))
    go' = foldr go'' (pure [])
    go'' (Node x xs) ys = liftA2 (:) (liftA2 Node (Lift (f x)) (later (go' xs))) ys
```

</details>
<details>
<summary>
Inline `go'` (and rename `go''` to `go'`)

</summary>

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))
    go' (Node x xs) ys = liftA2 (:) (liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))) ys
```

</details>
<details>
<summary>
Definition of `liftA2`

</summary>

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))
    go' (Node x xs) ys = liftA2 (:) (fmap Node (f x) :<*> (foldr go' (pure []) xs)) ys
```

</details>
<details>
<summary>
Definition of `liftA2` (pattern-matching on `ys`)

</summary>

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))
    go' (Node x xs) (Lift ys)    = fmap (((:).) . Node) (f x) :<*> (foldr go' (pure []) xs) <*> Lift ys
    go' (Node x xs) (ys :<*> zs) = fmap (((:).) . Node) (f x) :<*> (foldr go' (pure []) xs) <*> ys :<*> zs
```

</details>
<details>
<summary>
Definition of `<*>`.
</summary>

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))
    go' (Node x xs) (Lift ys)    = liftA2 flip (fmap (((:).) . Node) (f x)) ys :<*> foldr go' (pure []) xs
    go' (Node x xs) (ys :<*> zs) = liftA2 c (fmap (((:).) . Node) (f x)) ys :<*> liftA2 (,) (foldr go' (pure []) xs) zs
      where
        c f g ~(x,y) = f x (g y)
```

</details>
<details>
<summary>
Fuse `liftA2` with `fmap`

</summary>

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))
    go' (Node x xs) (Lift ys)    = liftA2 (flip . (((:).) . Node)) (f x) ys :<*> foldr go' (pure []) xs
    go' (Node x xs) (ys :<*> zs) = liftA2 (c . (((:).) . Node)) (f x) ys :<*> liftA2 (,) (foldr go' (pure []) xs) zs
      where
        c f g ~(x,y) = f x (g y)
```

</details>
<details open>
<summary>
Beta-reduction.
</summary>

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = go
  where
    go (Node x xs) = liftA2 Node (f x) (runPhases (foldr go' (pure []) xs))
    
    go' (Node x xs) (Lift ys)    = liftA2 (\y zs ys -> Node y ys : zs) (f x) ys :<*> foldr go' (pure []) xs
    go' (Node x xs) (ys :<*> zs) = liftA2 c (f x) ys :<*> liftA2 (,) (foldr go' (pure []) xs) zs
      where
        c y g ~(ys,z) = Node y ys : g z
```

</details>
At this point, we actually hit a wall: the expression

```haskell
liftA2 (,) (foldr go' (pure []) xs) zs
```

Is what makes the whole thing quadratic.
We need to find a way to thread that `liftA2` along with the fold to get it to
linear.
This is the only real trick in the derivation: we need to introduce it as an
existential to make the types line up.

```haskell
bft :: forall f a b. Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = go
  where
    go (Node x xs) = liftA2 (\y (ys,_) -> Node y ys) (f x) (runPhases (foldr go' (pure ([],())) xs))
    
    go' :: forall c. Tree a -> Phases f ([Tree b], c) -> Phases f ([Tree b], c)
    go' (Node x xs) ys@(Lift _)  = fmap (\y -> first (pure . Node y)) (f x) :<*> foldr go' ys xs
    go' (Node x xs) (ys :<*> zs) = liftA2 c (f x) ys :<*> foldr go' (fmap ((,) []) zs) xs
      where
        c y g ~(ys,z) = first (Node y ys:) (g z)
```
And that's it!

# Avoiding Maps

We can finally write a slightly different version that avoids some unnecessary
`fmap`s by basing `Phases` on `liftA2` rather than `<*>`.

```haskell
data Levels f a where
  Now   :: a -> Levels f a
  Later :: (a -> b -> c) -> f a -> Levels f b -> Levels f c

instance Functor f => Functor (Levels f) where
    fmap f (Now x) = Now (f x)
    fmap f (Later c xs ys) = Later ((f.) . c) xs ys
            
runLevels :: Applicative f => Levels f a -> f a
runLevels (Now x) = pure x
runLevels (Later f xs ys) = liftA2 f xs (runLevels ys)

bft :: forall f a b. Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = go
  where
    go (Node x xs) = liftA2 (\y (ys,_) -> Node y ys) (f x) (runLevels (foldr go' (Now ([],())) xs))
    
    go' :: forall c. Tree a -> Levels f ([Tree b], c) -> Levels f ([Tree b], c)
    go' (Node x xs) ys@(Now _)      = Later (\y -> first (pure . Node y)) (f x) (foldr go' ys xs)
    go' (Node x xs) (Later k ys zs) = Later id (liftA2 c (f x) ys) (foldr go' (fmap ((,) []) zs) xs)
      where
        c y g ~(ys,z) = first (Node y ys:) (k g z)
```

# References
