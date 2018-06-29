---
title: Probability 5 Ways
tags: Probability, Haskell
bibliography: Probability.bib
---

Ever since the famous pearl by @erwig_functional_2006, probabilistic programming
with monads has been an interesting and diverse area in functional programming,
with many different approaches.

I'm going to present five here, some of which I have not seen before.

# The Classic

As presented in the paper, the simple and elegant formulation of probability
distributions looks like this:

```haskell
newtype Prob a
    = Prob
    { runProb :: [(a, Rational)]
    }
```

Its monadic structure multiplies conditional events:

```haskell
instance Functor Prob where
    fmap f xs = Prob [ (f x, p) | (x,p) <- runProb xs ]
    
instance Applicative Prob where
    pure x = Prob [(x,1)]
    fs <*> xs
        = Prob
        [ (f x,fp*xp)
        | (f,fp) <- runProb fs
        , (x,xp) <- runProb xs ]
                     
instance Monad Prob where
    xs >>= f
        = Prob
        [ (y,xp*yp)
        | (x,xp) <- runProb xs
        , (y,yp) <- runProb (f x) ]
```

In most of the examples, we'll need a few extra functions in order for the types
to be useful. First is support:

```haskell
support :: Prob a -> [a]
support = fmap fst . runProb
```

And second is expectation:

```haskell
expect :: (a -> Rational) -> Prob a -> Rational
expect p xs = sum [ p x * xp | (x,xp) <- runProb xs ]

probOf :: (a -> Bool) -> Prob a -> Rational
probOf p = expect (bool 0 1 . p)
```

It's useful to be able to construct uniform distributions:

```haskell
uniform xs = Prob [ (x,n) | x <- xs ]
  where
    n = 1 % toEnum (length xs)
    
die = uniform [1..6]

>>> probOf (7==) $ do
  x <- die
  y <- die
  pure (x+y)
1 % 6
```

# The Bells and Whistles

As elegant as the above approach is, it leaves something to be desired when it
comes to efficiency. In particular, you'll see a combinatorial explosion at
every step. To demonstrate, let's take the example above, using three-sided dice
instead so it doesn't take up too much space.

```haskell
die = uniform [1..3]

example = do
  x <- die
  y <- die
  pure (x+y)
```

The probability table looks like this:

```{.center}
2 1/9
3 2/9
4 1/3
5 2/9
6 1/9
```

But the internal representation looks like this:

```
2 1/9
3 1/9
4 1/9
3 1/9
4 1/9
5 1/9
4 1/9
5 1/9
6 1/9
```

States are duplicated, because the implementation has no way of knowing that two
outcomes are the same. We could collapse equivalent outcomes if we used a
`Map`{.haskell}, but then we can't implement `Functor`{.haskell},
`Applicative`{.haskell}, or `Monad`{.haskell}. The types:

```haskell
class Functor f where
    fmap :: (a -> b) -> f a -> f b

class Functor f => Applicative f where
    pure :: a -> f a
    (<*>) :: f (a -> b) -> f a -> f b

class Applicative f => Monad f where
    (>>=) :: f a -> (a -> f b) -> f b
```

Don't allow an `Ord`{.haskell} constraint, which is what we'd need to remove
duplicates. We can instead make our own classes which *do* allow constraints:

```haskell
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies     #-}

import Prelude hiding (Functor(..),Applicative(..),Monad(..))

import Data.Kind

class Functor f where
    type Domain f a :: Constraint
    type Domain f a = ()
    fmap :: Domain f b => (a -> b) -> f a -> f b

class Functor f => Applicative f where
    {-# MINIMAL pure, liftA2 #-}
    pure   :: Domain f a => a -> f a
    liftA2 :: Domain f c => (a -> b -> c) -> f a -> f b -> f c
    
    (<*>) :: Domain f b => f (a -> b) -> f a -> f b
    (<*>) = liftA2 ($) 

class Applicative f => Monad f where
    (>>=) :: Domain f b => f a -> (a -> f b) -> f b

fail :: String -> a
fail = error

return :: (Applicative f, Domain f a) => a -> f a
return = pure
```

This setup gets over a couple common annoyances in Haskell, like making
[`Data.Set`{.haskell}](http://hackage.haskell.org/package/containers-0.6.0.1/docs/Data-Set.html)
a Monad:

```haskell
instance Functor Set where
    type Domain Set a = Ord a
    fmap = Set.map

instance Applicative Set where
    pure = Set.singleton
    liftA2 f xs ys = do
        x <- xs
        y <- ys
        pure (f x y)

instance Monad Set where
    (>>=) = flip foldMap
```

And, of course, the probability monad:

```haskell
newtype Prob a = Prob
    { runProb :: Map a Rational
    }

instance Functor Prob where
    type Domain Prob a = Ord a
    fmap f = Prob . Map.mapKeysWith (+) f . runProb

instance Applicative Prob where
    pure x = Prob (Map.singleton x 1)
    liftA2 f xs ys = do
      x <- xs
      y <- ys
      pure (f x y)
      
instance Ord a => Monoid (Prob a) where
    mempty = Prob Map.empty
    mappend (Prob xs) (Prob ys) = Prob (Map.unionWith (+) xs ys)

instance Monad Prob where
    Prob xs >>= f
        = Map.foldMapWithKey ((Prob .) . flip (Map.map . (*)) . runProb . f) xs

support = Map.keys . runProb

expect p = getSum . Map.foldMapWithKey (\k v -> Sum (p k * v)) . runProb

probOf p = expect (bool 0 1 . p)

uniform xs = Prob (Map.fromList [ (x,n) | x <- xs ])
  where
    n = 1 % toEnum (length xs)

ifThenElse True t _ = t
ifThenElse False _ f = f

die = uniform [1..6]

>>> probOf (7==) $ do
  x <- die
  y <- die
  pure (x + y)
1 % 6
```

# Free

Coming up with the right implementation all at once is quite difficult: luckily,
there are more general techniques for designing DSLs that break the problem into
smaller parts, which also give us some insight into the underlying composition
of the probability monad.

The technique relies on an algebraic concept called "free objects". A free
object for some class is a minimal implementation of that class. The classic
example is lists: they're the free monoid. Monoid requires that you have an
additive operation, an empty element, and that the additive operation be
associative. Lists have all of these things: what makes them *free*, though, is
that they have nothing else. For instance, the additive operation on lists
(concatenation) isn't commutative: if it was, they wouldn't be the free monoid
any more, because they satisfy an extra law that's not in monoid.

For our case, we can use the free monad: this takes a functor and gives it a
monad instance, in a way we know will satisfy all the laws. This encoding is
used in several papers [@scibior_practical_2015; @larsen_memory_2011].

The idea is to first figure out what primitive operation you need. We'll use
weighted choice:

```haskell
choose :: Prob a -> Rational -> Prob a -> Prob a
choose = ...
```

Then you encode it as a functor:

```haskell
data Choose a
    = Choose Rational a a
    deriving (Functor,Foldable)
```

We'll say the left-hand-choice has chance $p$, and the right-hand $1-p$. Then,
you just wrap it in the free monad:

```haskell
type Prob = Free Choose
```

And you already have a monad instance. Support comes from the
[`Foldable`{.haskell}](http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Foldable.html#v:toList)
instance:

```haskell
import Data.Foldable

support :: Prob a -> [a]
support = toList
```

Expectation is an "interpreter" for the DSL:

```haskell
expect :: (a -> Rational) -> Prob a -> Rational
expect p = iter f . fmap p
  where
    f (Choose c l r) = l * c + r * (1-c)
```

For building up the tree, we can use Huffman's algorithm:

```haskell
fromList :: (a -> Rational) -> [a] -> Prob a
fromList p = go . foldMap (\x -> singleton (p x) (Pure x))
  where
    go xs = case minView xs of
      Nothing -> error "empty list"
      Just ((xp,x),ys) -> case minView ys of
        Nothing -> x
        Just ((yp,y),zs) ->
            go (insertHeap (xp+yp) (Free (Choose (xp+yp) x y)) zs)
```

And finally, it gets the same notation as before:

```haskell
uniform = fromList (const 1)

die = uniform [1..6]

probOf p = expect (bool 0 1 . p)

>>> probOf (7==) $ do
  x <- die
  y <- die
  pure (x + y)
1 % 6
```

One of the advantages of the free approach is that it's easy to define multiple
interpreters. We could, for instance, write an interpreter that constructs a
diagram:

```haskell
>>> drawTree ((,) <$> uniform "abc" <*> uniform "de")
           ┌('c','d')
     ┌1 % 2┤
     │     └('c','e')
1 % 3┤
     │           ┌('a','d')
     │     ┌1 % 2┤
     │     │     └('a','e')
     └1 % 2┤
           │     ┌('b','d')
           └1 % 2┤
                 └('b','e')
```

# Final

There's a lot to be said about free objects in category theory, also.
Specifically, they're related to initial and terminal (also called final)
objects. The encoding above is initial, the final encoding is simply
`Cont`{.haskell}:

```haskell
newtype Cont r a = Cont { runCont :: (a -> r) -> r }

type Prob = Cont Rational
```

Here, also, we get the monad instance for free. In contrast to previously,
expect is free:

```haskell
expect = flip runCont
```

Support, though, isn't possible.

# Cofree

The branching structure of the tree captures the semantics of the probability
monad well, but it doesn't give us much insight into the original
implementation. The question is, how can we deconstruct this:

```haskell
newtype Prob a
    = Prob
    { runProb :: [(a, Rational)]
    }
```

Eric Kidd -@kidd_build_2007 pointed out that the monad is the composition of the
writer and list monads:

```haskell
type Prob = WriterT (Product Rational) []
```

but that seems unsatisfying: in contrast to the tree-based version, we don't
encode any branching structure, we're able to have empty distributions, and it
has the combinatorial explosion problem.

Adding a weighting to nondeterminism is encapsulated more concretely by the
`ListT`{.haskell} transformer. It looks like this:

```haskell
newtype ListT m a
    = ListT
    { runListT :: m (Maybe (a, ListT m a))
    }
```

It's a cons-list, with an effect before every layer[^done-right]. 

[^done-right]: Note this is *not* the same as the `ListT`{.haskell} in
    [transformers](http://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-List.html);
    instead it's a "[ListT done
    right](https://wiki.haskell.org/ListT_done_right)".

While this can be used to give us the monad we need, I've found that something
more like this fits the abstraction better:

```haskell
data ListT m a
    = ListT a (m (Maybe (ListT m a)))
```

It's a nonempty list, with the first element exposed. Turns out this is very
similar to the cofree comonad:

```haskell
data Cofree f a = a :< f (Cofree f a)
```

Just like the initial free encoding, we can start with a primitive operation:

```haskell
data Perhaps a
    = Impossible
    | WithChance Rational a
    deriving (Functor,Foldable)
```

And we get all of our instances as well:

```haskell
newtype Prob a
    = Prob
    { runProb :: Cofree Perhaps a
    } deriving (Functor,Foldable)
    
instance Comonad Prob where
    extract (Prob xs) = extract xs
    duplicate (Prob xs) = Prob (fmap Prob (duplicate xs))

foldProb :: (a -> Rational -> b -> b) -> (a -> b) -> Prob a -> b
foldProb f b = r . runProb
  where
    r (x :< Impossible) = b x
    r (x :< WithChance p xs) = f x p (r xs)

uniform :: [a] -> Prob a
uniform (x:xs) = Prob (coiterW f (EnvT (length xs) (x :| xs)))
  where
    f (EnvT 0 (_ :| [])) = Impossible
    f (EnvT n (_ :| (y:ys))) 
        = WithChance (1 % fromIntegral n) (EnvT (n - 1) (y:|ys))

expect :: (a -> Rational) -> Prob a -> Rational
expect p = foldProb f p
  where
    f x n xs = (p x * n + xs) / (n + 1)

probOf :: (a -> Bool) -> Prob a -> Rational
probOf p = expect (\x -> if p x then 1 else 0)

instance Applicative Prob where
    pure x = Prob (x :< Impossible)
    (<*>) = ap
    
append :: Prob a -> Rational -> Prob a -> Prob a
append = foldProb f (\x y ->  Prob . (x :<) . WithChance y . runProb)
  where
    f e r a p = Prob . (e :<) . WithChance ip . runProb . a op
      where
        ip = p * r / (p + r + 1)
        op = p / (r + 1)

instance Monad Prob where
    xs >>= f = foldProb (append . f) f xs
```

The application of comonads to streams (`ListT`{.haskell}) has been explored
before [@uustalu_essence_2005]; I wonder if there are any insights to be gleaned
from this particular probability comonad.

# References
