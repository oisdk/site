---
title: An Efficient Queue of Applicative Effects
tags: Haskell
series: Breadth-First Traversals
bibliography: Applicative Queue.bib
---

We pick up the story again at the question of a breadth-first (Applicative)
traversal of a rose tree [@gibbons_breadthfirst_2015].
In the last post, I finally came up with an implementation I was happy with:

```haskell
data Tree a = a :& [Tree a]

bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f (x :& xs) = liftA2 (:&) (f x) (bftF f xs)

bftF :: Applicative f => (a -> f b) -> [Tree a] -> f [Tree b]
bftF t = fmap head . foldr (<*>) (pure []) . foldr f [pure ([]:)]
  where
    f (x :& xs) (q : qs) = liftA2 c (t x) q : foldr f (p qs) xs
    
    p []     = [pure ([]:)]
    p (x:xs) = fmap (([]:).) x : xs

    c x k (xs : ks) = ((x :& xs) : y) : ys
      where (y : ys) = k ks
```

It has the correct semantics and asymptotics.

```haskell
tree =
    1 :&
      [ 2 :&
          [ 5 :&
              [ 9  :& []
              , 10 :& []]
          , 6 :& []]
      , 3 :& []
      , 4 :&
          [ 7 :&
              [ 11 :& []
              , 12 :& []]
          , 8 :& []]]
          
>>> bft print tree
1
2
3
4
5
6
7
8
9
10
11
12
() :&
   [ () :&
        [ () :&
             [ () :& []
             , () :& []]
        , () :& []]
   , () :&   []
   , () :&
        [ () :&
             [ () :& []
             , () :& []]
        , () :& []]]
```

But it's quite difficult to understand, and doesn't lend much insight into
what's going on with the whole "breadth-first" notion.
The technique the function uses also isn't reusable.

A much nicer function uses the `Phases` Applicative [@easterly_functions_2019]:

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runPhases . go
  where
    go (Node x xs) = liftA2 Node (Lift (f x)) (later (traverse go xs))
```

But this function is quadratic.

So the task for this post today is to derive a type like the `Phases` type with
a `later` operation, but which has the appropriate performance characteristics.
At the end I'll look into what the theoretical properties of this type are.

# A Free Applicative

At its core, the `Phases` type is basically a free Applicative
[@capriotti_free_2014].
I'll reimplement it here as a slightly different free Applicative (one that's
based on `liftA2` rather than `<*>`):

```haskell
data Free f a where
  Pure :: a -> Free f a
  Appl :: (a -> b -> c) -> f a -> Free f b -> Free f c

runFree :: Applicative f => Free f a -> f a
runFree (Pure x)      = pure x
runFree (Appl f x xs) = liftA2 f x (runFree xs)
```

The key with the `Phases` type is to observe that there's actually two possible
implementations of `Applicative` for the `Free` type above: one which makes it
the "correct" free applicative:

```haskell
instance Applicative (Free f) where
  pure = Pure

  liftA2 c (Pure x) ys = fmap (c x) ys
  liftA2 c (Appl f x xs) ys = Appl (\x (y,z) -> c (f x y) z) x (liftA2 (,) xs ys)
```

And then one which *zips* effects together:

```haskell
instance Applicative f => Applicative (Free f) where
  pure = Pure
  
  liftA2 c (Pure x) ys = fmap (c x) ys
  liftA2 c xs (Pure y) = fmap (flip c y) xs
  liftA2 c (Appl f x xs) (Appl g y ys) = 
    Appl 
      (\(x,y) (xs,ys) -> c (f x xs) (g y ys)) 
      (liftA2 (,) x y) 
      (liftA2 (,) xs ys)
```

This second instance makes the `Free` type into not a free Applicative at all:
instead it's some kind of Applicative transformer which we can use to reorder
effects.
Since effects are combined only when they're at the same point in the list, we
can use it to do our breadth-first traversal.

As an aside, from this perspective it's clear that this is some kind of
`FunList` [@vanlaarhoven_nonregular_2009]: this opens up a lot of interesting
curiosities about the type, since that type in particular is quite well-studied.

Anyway, we're able to do the `later` operation quite simply:

```haskell
later :: Free f a -> Free f a
later = Appl (const id) (pure ())
```

# Making it Efficient

The problem at the moment is that the Applicative instance has an
$\mathcal{O}(n)$ `liftA2` implementation: this translates into an
$\mathcal{O}(n^2)$ traversal overall.

If we were working in a more simple context of just enumerating the contents of
the tree, we might at this point look to something like difference lists: these
use the cayley transform on the list monoid to turn the append operation from
$\mathcal{O}(n)$ to $\mathcal{O}(n^2)$.
It turns out that there is a similar cayley transformation for Applicative
functors [@rivas_notions_2014; @rivas_monoids_2015]:

```haskell
newtype Day f a = Day { runDay :: forall b. f b -> f (a, b) }

instance Functor f => Functor (Day f) where
  fmap f xs = Day (fmap (first f) . runDay xs)
  
instance Functor f => Applicative (Day f) where
  pure x = Day (fmap ((,) x))
  liftA2 c xs ys = Day (fmap (\(x,(y,z)) -> (c x y, z)) . runDay xs . runDay ys)
```

And with this type we can implement our queue of applicative effects:

```haskell
type Q f = Day (Free f)

runQ :: Applicative f => Q f a -> f a
runQ = fmap fst . runFree . flip runDay (Pure ())

now :: Applicative f => f a -> Q f a
now xs = Day \case
  Pure x      -> Appl (,) xs (Pure x)
  Appl f y ys -> Appl (\(x,y) z -> (x, f y z)) (liftA2 (,) xs y) ys

later :: Applicative f => Q f a -> Q f a
later xs = Day \case
  Pure x      -> Appl (const id) (pure ()) (runDay xs (Pure x))
  Appl f y ys -> Appl (\x (y,z) -> (y, f x z)) y (runDay xs ys)
```

As expected, this gives us the clean implementation of a breadth-first traversal
with the right asymptotics (I think):

```haskell
bft :: Applicative f => (a -> f b) -> Tree a -> f (Tree b)
bft f = runQ . go
  where
    go (x :& xs) = liftA2 (:&) (now (f x)) (later (traverse go xs))
```

(it's worth pointing out that we haven't actually used the applicative instance
on the free applicative at any point: we have inlined all of the "zipping" to
make it absolutely clear that everything has stayed linear).

# So what's the Theory?

I have yet to really dive deep on any of the theory involved in this type, I
just quickly wrote up this post when I realised I was able to use the cayley
transform from the mentioned papers to implement the proper breadth-first
traversal.
It certainly seems worth looking at more!

# References
