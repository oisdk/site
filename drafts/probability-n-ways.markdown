---
title: Probability 5 Ways
tags: Probability, Haskell
bibliography: Probability.bib
---

Ever since the famous pearl by @erwig_functional_2006, probabilistic programming
with monads has been an interesting and diverse area in functional programming,
with many different approaches.

I'm going to present six here, some of which I have not seen before.

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
    fs <*> xs = Prob [ (f x,fp*xp)
                     | (f,fp) <- runProb fs
                     , (x,xp) <- runProb xs ]
                     
instance Monad Prob where
    xs >>= f = Prob [ (y,xp*yp)
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
```

It's useful to be able to construct uniform distributions:

```haskell
uniform xs = Prob [ (x,n) | x <- xs ]
  where
    n = 1 % toEnum (length xs)
    
die = uniform [1..6]

>>> expect id $ do
  x <- die
  y <- die
  pure $  if (x + y) == 7 then 1 else 0
1 % 6
```

# The Bells and Whistles

As elegant as the above approach is, it leaves something to be desired when it
comes to efficiency. In particular, you'll see a combinatorial explosion where
more efficient implementations might compress the representation at every step.
We can accomplish the compression with some modern GHC features:

```haskell
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies     #-}

import Prelude hiding (Functor(..),Applicative(..),Monad(..))

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import           Data.Kind
import           Data.Monoid
import           Data.Ratio

newtype Prob a
    = Prob
    { runProb :: Map a Rational
    }

fail = error
return = pure

class Functor f where
    type Domain f a :: Constraint
    fmap :: Domain f b => (a -> b) -> f a -> f b

class Functor f => Applicative f where
    pure :: Domain f a => a -> f a
    liftA2 :: Domain f c => (a -> b -> c) -> f a -> f b -> f c

class Applicative f => Monad f where
    (>>=) :: Domain f b => f a -> (a -> f b) -> f b

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

uniform xs = Prob (Map.fromList [ (x,n) | x <- xs ])
  where
    n = 1 % toEnum (length xs)

ifThenElse True t _ = t
ifThenElse False _ f = f

die = uniform [1..6]

>>> expect id $ do
  x <- die
  y <- die
  pure $  if (x + y) == 7 then 1 else 0
1 % 6
```

# Initially Free

As it turns out, compression at each level doesn't give you the speedup you
might hope for. Another approach which is potentially more promising is to put
off running the computation until as late as possible, using a free
representation of some sort. Which free representation to choose is an
interesting question: taking something like the
[operational](http://hackage.haskell.org/package/operational) approach we can
first decide what primitives we need, and then just wrap that in
`Free`{.haskell}.

The primitive operation focused on in several papers [@scibior_practical_2015;
@larsen_memory_2011] is weighted choice:

```haskell
choose :: Prob a -> Rational -> Prob a -> Prob a
choose = ...
```

We can encode this as a data constructor:

```haskell
data Choose a
    = Choose Rational a a
    deriving (Functor,Foldable)
```

We'll say the left-hand-choice has chance $p$, and the right-hand $1-p$. The
actual prob type itself is:

```haskell
type Prob = Free Choose
```

The monad instance is free, and support comes from the
[`Foldable`{.haskell}](http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Foldable.html#v:toList)
instance (also free):

```haskell
import Data.Foldable

support :: Prob a -> [a]
support = toList
```

Expectation is manual, though:

```haskell
expect :: (a -> Rational) -> Prob a -> Rational
expect p = iter f . fmap p
  where
    f (Choose c l r) = l * c + r * (1-c)
```

But we can use Huffman's algorithm to build up the tree:

```haskell
fromList :: (a -> Rational) -> [a] -> Prob a
fromList p = go . foldMap (\x -> singleton (p x) (Leaf w x))
  where
    go xs = case minView xs of
      Nothing -> error "empty list"
      Just ((xp,x),ys) -> case minView ys of
        Nothing -> x
        Just ((yp,y),zs) -> go (insertHeap (xp+yp) (Node (xp+yp) x y) zs)
```

And it gets the same notation as before:

```haskell
uniform = fromList (const 1)

die = uniform [1..6]

>>> expect id $ do
  x <- die
  y <- die
  pure $  if (x + y) == 7 then 1 else 0
1 % 6
```

And we can use it to diagram the process:

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

# Finally Free

The other main way to construct free objects is in the final encoding:

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

As well as a monadic structure, probability distributions have a comonadic
structure. Again, like the initial free encoding, we begin with a functor to
describe the primitive operation:

```haskell
data Event a = Impossible
             | WithOdds Rational a
             deriving (Functor,Foldable)
```

This version looks more like a cons-list than the free construction:

```haskell
newtype Prob a
    = Prob
    { runProb :: Cofree Event a
    } deriving (Functor,Foldable)
    
instance Comonad Prob where
    extract (Prob xs) = extract xs
    duplicate (Prob xs) = Prob (fmap Prob (duplicate xs))

uniform :: [a] -> Prob a
uniform (x:xs) = Prob (coiterW f (EnvT (length xs) (x :| xs)))
  where
    f (EnvT 0 (_ :| [])) = Impossible
    f (EnvT n (_ :| (y:ys))) = WithOdds (1 % fromIntegral n) (EnvT (n - 1) (y:|ys))

expect :: (a -> Rational) -> Prob a -> Rational
expect p = go . runProb where
  go (x :< WithOdds n xs) =  (p x * n + go xs) / (n + 1)
  go (x :< Impossible) =  p x

probOf :: (a -> Bool) -> Prob a -> Rational
probOf p = expect (\x -> if p x then 1 else 0)

instance Applicative Prob where
  pure x = Prob (x :< Impossible)
  (<*>) = ap

instance Monad Prob where
  Prob xs >>= f = Prob (go xs)
    where
      go (x :< Impossible) = runProb (f x)
      go (x :< WithOdds p xs) = append (runProb (f x)) p (go xs)
      append = foldOdds f (\x y xs ->  x :< WithOdds y xs) where
        f e r a p ys = e :< WithOdds ip (a op ys) where
          ip = p * r / (p + r + 1)
          op = p / (r + 1)
      foldOdds f b = r where
        r (x :< Impossible) = b x
        r (x :< WithOdds p xs) = f x p (r xs)
```
