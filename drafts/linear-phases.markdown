---
title: Linear-Time Phases
series: Breadth-First Traversals
tags: Haskell
bibliography: Rose Tree Traversals.bib
---

Today, I'm going to be looking at the `Phases` applicative:

```haskell
data Phases f a where
  Lift   :: f a -> Phases f a
  (:<*>) :: f (a -> b) -> Phases f a -> Phases f b
```

And I'm going to see how to use it to write a linear-time breadth-first
traversal.

Remembering from last time, the key component of the phases type is that it
combines applicative effects in parallel:

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

This, combined with a couple helper functions:

```haskell
runPhases :: Applicative f => Phases f a -> f a
runPhases (Lift x) = x
runPhases (fs :<*> xs) = fs <*> runPhases xs

later :: Applicative f => Phases f a -> Phases f a
later = (:<*>) (pure id)
```

Makes for the clear and elegant following function:

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (traverse go xs))
```

# Performance

Hidden in the `traverse` above is a sequence of very expensive calls to `<*>`.
It's analogous to the breadth-first enumeration from
@gibbons_breadth-first_2015:

```haskell
levels :: Tree a -> [[a]]
levels (Node x xs) = [x] : foldr lzw [] (map levels xs)
  where
    lzw [] ys = ys
    lzw xs [] = xs
    lzw (x:xs) (y:ys) = (x ++ y) : lzw xs ys
```

Here, `lzw` takes the place of `<*>`.
`lzw` is linear, though, making the whole thing quadratic.
But we know how to improve it, with the following function:

```haskell
levels :: Tree a -> [[a]]
levels ts = f ts []
  where
    f (Node x xs) (q:qs) = (x:q) : foldr f qs xs
    f (Node x xs) []     = [x]   : foldr f [] xs
```

This effectively fuses the zip with the levels function itself, getting us back
linear time.
Can we do the same for `Phases`?

Firstly, let's inline some of the functions in `bft`, to expose the `foldr` on
the list.

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (go' xs))
    go' = foldr (liftA2 (:) . go) (pure [])
```

We're trying to get it as close to the fast levels definition above as possible,
so let's fiddle with it a little more.

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))
    go' (Node x xs) ys = liftA2 (:) (liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))) ys
```

Now let's inline some of the `Phases` functions.

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))
    go' (Node x xs) ys = liftA2 (:) (fmap Node (f x) :<*> (foldr go' (pure []) xs)) ys
```

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (foldr go' (pure []) xs))
    go' (Node x xs) (Lift ys)    = fmap (((:).) . Node) (f x) :<*> (foldr go' (pure []) xs) <*> Lift ys
    go' (Node x xs) (ys :<*> zs) = fmap (((:).) . Node) (f x) :<*> (foldr go' (pure []) xs) <*> ys :<*> zs
```

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

It's at this point that we hit a wall.
The quadratic call is still present.
Removing it requires polymorphic recursion in `go'`:

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

Finally, to avoid any expense that might be incurred from unnecessary `fmap`s,
we will use a different `Phases` type:

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
