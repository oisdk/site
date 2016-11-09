---
title: Semirings
tags: Haskell
bibliography: Semirings.bib
---
```{.haskell .literate .hidden_source}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms, ViewPatterns, LambdaCase #-}
{-# LANGUAGE RankNTypes, FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Semirings where

import qualified Data.Map.Strict as Map
import Data.Monoid
import Data.Array
import Data.Foldable
import Data.Ratio
import Control.Applicative
import Control.Arrow (first)
import Control.Monad.Cont
import Data.Functor.Identity
import GHC.Exts
import Data.Maybe
import Data.List hiding (insert)
```

I've been playing around a lot with [semirings](https://en.wikipedia.org/wiki/Semiring) recently. A semiring is anything with addition, multiplication, zero and one. You can represent that in Haskell as:


```{.haskell .literate}
class Semiring a where
  zero :: a
  one  :: a
  infixl 7 <.>
  (<.>) :: a -> a -> a
  infixl 6 <+>
  (<+>) :: a -> a -> a
```

It's kind of like a combination of two  [monoids](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Monoid.html). It has the normal monoid laws:

```{.haskell}
x <+> (y <+> z) = (x <+> y) <+> z
x <.> (y <.> z) = (x <.> y) <.> z
x <+> zero = zero <+> x = x
x <.> one  = one  <.> x = x
```

And a few extra:

```{.haskell}
x <+> y = y <+> x
x <.> (y <+> z) = (x <.> y) <+> (x <.> z)
(x <+> y) <.> z = (x <.> z) <+> (y <.> z)
zero <.> a = a <.> zero = zero
```

At first glance, it looks quite numeric. Indeed, [PureScript](https://pursuit.purescript.org/packages/purescript-prelude/1.1.0/docs/Data.Semiring) uses it as the basis for its numeric hierarchy. It certainly works a lot nicer than Haskell's [`Num`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Prelude.html#g:5).

```{.haskell .literate}
instance Semiring Integer where
  zero = 0
  one  = 1
  (<+>) = (+)
  (<.>) = (*)

instance Semiring Double where
  zero = 0
  one  = 1
  (<+>) = (+)
  (<.>) = (*)
```

However, `Bool`{.haskell} also conforms:

```{.haskell .literate}
instance Semiring Bool where
  zero = False
  one  = True
  (<+>) = (||)
  (<.>) = (&&)
```

And it lets you define nicer `Sum`{.haskell} and `Product`{.haskell} newtypes:

```{.haskell .literate}
newtype Add a = Add
  { getAdd :: a
  } deriving (Eq, Ord, Read, Show)

newtype Mul a = Mul
  { getMul :: a
  } deriving (Eq, Ord, Read, Show)
             
instance Semiring a => Monoid (Add a) where
  mempty = Add zero
  Add x `mappend` Add y = Add (x <+> y)

instance Semiring a => Monoid (Mul a) where
  mempty = Mul one
  Mul x `mappend` Mul y = Mul (x <.> y)
  
add :: (Semiring a, Foldable f) => f a -> a
add = getAdd . foldMap Add

mul :: (Semiring a, Foldable f) => f a -> a
mul = getMul . foldMap Mul
```
```{.haskell .literate .prop}
add xs == sum (xs :: [Integer])
```
```{.haskell .literate .prop}
mul xs == product (xs :: [Integer])
```
Which subsume `Any`{.haskell} and `All`{.haskell}:
```{.haskell .literate .prop}
add xs == any id (xs :: [Bool])
```
```{.haskell .literate .prop}
mul xs == all id (xs :: [Bool])
```

So far, so easy.

## A Semiring Map

I got using semirings first to try and avoid code duplication for a trie implementation. Basically, I wanted to write one map-like type, and have its behaviour change between the whole Boom hierarchy [@bunkenburg_boom_1994] depending on the type annotations. I also wanted to avoid newtypes.

```{.haskell .literate}
newtype GeneralMap a b = GeneralMap
  { getMap :: Map.Map a b
  } deriving (Functor, Show, Eq, Ord)

lookup :: (Ord a, Monoid b) => a -> GeneralMap a b -> b
lookup x = fold . Map.lookup x . getMap

assoc :: (Ord a, Applicative f, Monoid (f b)) 
      => a -> b -> GeneralMap a (f b) -> GeneralMap a (f b)
assoc k v = GeneralMap . Map.insertWith mappend k (pure v) . getMap

delete :: Ord a => a -> GeneralMap a b -> GeneralMap a b
delete x = GeneralMap . Map.delete x . getMap
```

That will give you a couple of flexible type synonyms:

```{.haskell .literate}
type Map a b = GeneralMap a (First b)
type MultiMap a b = GeneralMap a [b]
```

Which can specialise the functions to these types:

```{.haskell}
lookup :: Ord a => a -> Map a b -> First b
assoc  :: Ord a => a -> b -> Map a b -> Map a b
delete :: Ord a => a -> Map a b -> Map a b

lookup :: Ord a => a -> MultiMap a b -> [b]
assoc  :: Ord a => a -> b -> MultiMap a b -> MultiMap a b
delete :: Ord a => a -> MultiMap a b -> MultiMap a b
```

Sets need `one`{.haskell}, though:

```{.haskell .literate}
insert :: (Ord a, Semiring b) => a -> GeneralMap a b -> GeneralMap a b
insert x = GeneralMap . Map.insertWith (<+>) x one . getMap
```
```{.haskell}
type Set      a = GeneralMap a (Add Bool)
type MultiSet a = GeneralMap a (Add Integer)
```

And the signatures specialize nicely:

```{.haskell}
insert :: Ord a => a -> Set a -> Set a

insert :: Ord a => a -> MultiSet a -> MultiSet a
```

Some more operations which might be useful:

```{.haskell .literate}
fromList :: (Ord a, Semiring b, Foldable f) => f a -> GeneralMap a b
fromList = foldr insert (GeneralMap Map.empty)

fromAssocs :: (Ord a, Applicative f, Monoid (f b), Foldable t) 
           => t (a, b) -> GeneralMap a (f b)
fromAssocs = foldr (uncurry assoc) (GeneralMap Map.empty)

instance (Ord a, Monoid b) => Monoid (GeneralMap a b) where
  mempty = GeneralMap Map.empty
  mappend (GeneralMap x) (GeneralMap y) = 
    GeneralMap (Map.unionWith mappend x y)
```

That's about as far as I got, though. In particular, intersection wasn't very easy to define:

```{.haskell .literate}
intersection :: (Ord a, Semiring b)
             => GeneralMap a b -> GeneralMap a b -> GeneralMap a b
intersection (GeneralMap x) (GeneralMap y) =
  GeneralMap (Map.intersectionWith (<.>) x y)
```

While it works for `Set`s, it doesn't make sense for `MultiSet`s, and it doesn't work for `Map`s. I couldn't find a more suitable semiring in order to represent what I wanted. (I'm probably after a different algebraic structure) 

## A Probability Semiring

While searching, though, I came across some other interesting semirings. The *Probability* semiring, in particular, was pretty interesting. It's just the normal semiring over the rationals, with a lower bound of 0, and an upper of 1. You could combine it with a list to get the traditional probability monad: there's an example in PureScript's [Distributions](https://pursuit.purescript.org/packages/purescript-distributions/) package.

The normal, standard definition of probability is this:

```{.haskell}
newtype Prob s a = Prob { runProb :: [(a, s)]}
```

Fiddling with that definition can get you some pretty cool definitions. For instance, you can build the monad out of smaller transformers:

```{.haskell}
WriterT (Product Double) []
```

Eric Kidd describes it as `PerhapsT`{.haskell}: a `Maybe`{.haskell} with attached probability in his [excellent blog post](http://www.randomhacks.net/2007/02/21/refactoring-probability-distributions/).

Of course, the boring version:

```{.haskell}
newtype Prob s a = Prob { runProb :: [(a, s)]}
```

Looks like an inefficient version of a `Map`. Or, to put it a different way, the general map from above.

## Cont

Edward Kmett [-@kmett_modules_2011] pointed out that this can be expressed as:

```{.haskell}
infixr 0 $*
newtype Linear r a = Linear { ($*) :: (a -> r) -> r }
```

Or, as it's also known: [Cont](https://hackage.haskell.org/package/mtl-2.2.1/docs/Control-Monad-Cont.html#t:Cont). This can actually encode all the functionality you might need: (and even a sensible `<|>`{.haskell} definition)

```{.haskell .literate}
fromProbs :: (Semiring s, Applicative m) => [(a,s)] -> ContT s m a
fromProbs xs = ContT $ \k ->
  foldr (\(x,s) a -> liftA2 (<+>) (fmap (s<.>) (k x)) a) (pure zero) xs

instance (Semiring r, Applicative m) => Alternative (ContT r m) where
  f <|> g = ContT (\k -> (<+>) <$> runContT f k <*> runContT g k)
  empty = ContT (const (pure zero))

probOfT :: (Semiring r, Applicative m) => (a -> Bool) -> ContT r m a -> m r
probOfT e c = runContT c (\x -> if e x then pure one else pure zero)

probOf :: Semiring r => (a -> Bool) -> Cont r a -> r
probOf e = runIdentity . probOfT e

uniform :: Applicative m => [a] -> ContT Double m a
uniform xs =
  let s = 1.0 / fromIntegral (length xs)
  in fromProbs (map (flip (,) s) xs)
```

I wonder if this representation has something to do with modules over monads [@hirschowitz_modules_2010].

In fact, you can beef up the `<|>`{.haskell} operator a little, with something like [the conditional choice operator](http://zenzike.com/posts/2011-08-01-the-conditional-choice-operator):

```{.haskell .literate}
data BiWeighted s = s :|: s
infixl 8 :|:

(|>) :: (Applicative m, Semiring s)
     => BiWeighted s
     -> ContT s m a
     -> ContT s m a
     -> ContT s m a
((lp :|: rp) |> r) l =
  (mapContT.fmap.(<.>)) lp l <|> (mapContT.fmap.(<.>)) rp r
--
(<|) :: ContT s m a
     -> (ContT s m a -> ContT s m a)
     -> ContT s m a
l <| r = r l

infixr 0 <|
infixr 0 |>
```
```{.haskell .literate .example}
probOf ('a'==) (uniform "a" <| 0.4 :|: 0.6 |> uniform "b")
0.4
```

## UnLeak

Another optimization is to transform the leaky [`WriterT`](https://twitter.com/gabrielg439/status/659170544038707201) into a state monad:

```{.haskell .literate}
newtype WeightedT s m a = WeightedT 
  { getWeightedT :: s -> m (a, s)
  } deriving Functor
  
instance Monad m => Applicative (WeightedT s m) where
  pure x = WeightedT $ \s -> pure (x,s)
  WeightedT fs <*> WeightedT xs = WeightedT $ \s -> do
    (f, p) <- fs s
    (x, t) <- xs p
    pure (f x, t)
  
instance Monad m => Monad (WeightedT s m) where
  WeightedT x >>= f = WeightedT $ \s -> do
    (x, p) <- x s
    getWeightedT (f x) p
```

(I think this might have something to do with Cont) You can even make it look like a normal (non-transformer) writer with some pattern synonyms:

```{.haskell .literate}
type Weighted s = WeightedT s Identity

pattern Weighted w <- (runIdentity . flip getWeightedT zero -> w) where
  Weighted (x,w) = WeightedT (\s -> Identity (x, s <.> w) )
```

And you can pretend that you've just got a normal tuple:

```{.haskell .literate}
half :: a -> Weighted Double a
half x = Weighted (x, 0.5)

runWeighted :: Semiring s => Weighted s a -> (a, s)
runWeighted (Weighted w) = w

evalWeighted :: Semiring s => Weighted s a -> a
evalWeighted (Weighted (x,_)) = x

execWeighted :: Semiring s => Weighted s a -> s
execWeighted (Weighted (_,s)) = s
```

## Free

Looking back at `Cont`, it is reminiscent of an initial encoding of the free monoid:

```{.haskell}
newtype FreeMonoid a = FreeMonoid
  { forall m. Monoid m => (a -> m) -> m }
```

[@doel_free_2015]

So this big map-like thing, which represents probability, and continuations, and whatnot, has something to do with the free semiring.

Another encoding which looks free-ish is one of the efficient implementations of the probability monad:

```{.haskell}
data Dist a where
  Certainly :: a -> Dist a -- only possible value
  Choice :: Probability -> Dist a -> Dist a -> Dist a
  Fmap ::(a -> b) -> Dist a -> Dist b
  Join :: Dist (Dist a) -> Dist a
```

[@larsen_memory_2011]

It looks like almost a semigroup in the category of endofunctors! [@rivas_monoids_2015] Alternatively it resembles a free `MonadPlus`{.haskell}, although that's probably misleading. You need an extra law to make even a *near*-semiring, and most members of the above classes *don't* follow that extra law. The only things which really do are basically lists! (Edward Kmett has an explanation [here](https://www.reddit.com/r/haskell/comments/3dlz6b/from_monoids_to_nearsemirings_the_essence_of/ct6mr0g/))

An actual free near-semiring looks like this:

```{.haskell}
data Free f x = Free {unFree :: [FFree f x] }
data FFree f x = Pure x | Con (f (Free f x))
```

[@rivas_monoids_2015]

Specialized to the `Identity`{.haskell} monad, that becomes:

```{.haskell}
data Forest a = Forest { unForest :: [Tree x] }
data Tree x = Leaf x | Branch (Forest x)
```

De-specialized to the [free monad transformer](https://hackage.haskell.org/package/free-4.12.4/docs/Control-Monad-Trans-Free.html), it becomes:

```{.haskell}
newtype FreeT f m a = FreeT
  { runFreeT :: m (FreeF f a (FreeT f m a)) }

data FreeF f a b
  = Pure a
  | Free (f b)

type FreeNearSemiring f = FreeT f []
```

These definitions all lend themselves to combinatorial search [@spivey_algebras_2009, @fischer_reinventing_2009, @piponi_monad_2009], with one extra operation needed: `wrap`{.haskell}.

## Odds

Does `Odds`{.haskell} fit in to any of this?

While `WriterT (Product Rational) []`{.haskell} is a valid definition of the traditional probability monad, it's *not* the same as the `Odds`{.haskell} monad. If you take the odds monad, and parameterize it over the weight of the tail, you get this:

```{.haskell}
data Odds m a = Certain a | Choice (m (a, Odds a))
```

Which looks remarkably like [`ListT`{.haskell} done right](https://wiki.haskell.org/ListT_done_right):

```{.haskell .literate}
newtype ListT m a = ListT { next :: m (Step m a) }
data Step m a = Cons a (ListT m a) | Nil
```

(I'm using [Gabriel Gonzalez](http://www.haskellforall.com/2016/07/list-transformer-beginner-friendly-listt.html)'s version here)

Except that it allows empty lists. It looks like you can express the relationship between probability and odds as:

```{.haskell}
WriterT (Product  Rational) [] = Probability
ListT   (Weighted Rational)    = Odds
```

To disallow empty lists, you can use the [Cofree Comonad](https://hackage.haskell.org/package/free-4.12.4/docs/Control-Comonad-Cofree.html):

```{.haskell .literate}
data Cofree f a = a :< (f (Cofree f a))
```

Subbing in `Maybe`{.haskell} for `f`{.haskell}, you get a non-empty list. A *weighted* `Maybe`{.haskell} is basically [`PerhapsT`{.haskell}](http://www.randomhacks.net/2007/02/21/refactoring-probability-distributions/), as was mentioned earlier.

## Generalizing Semirings

As you might have noticed, semirings seem to have a lot to do with "both" and "either" things. For instance: `Arrow`, `ArrowChoice`; `Monad`, `MonadPlus`; `Applicative`, `Alternative`; `List`, `ZipList`, etc. Becoming more general still, you can describe types as a semiring:

```{.haskell}
(<.>) = (,)
one = ()

(<+>) = Either
zero = Void
```

There's a subset of semirings which are [star semirings](https://en.wikipedia.org/wiki/Semiring#Star_semirings). They have an operation $*$ such that:

$a* = 1 + aa* = 1 + a*a$

Or, as a class:

```{.haskell .literate}
class Semiring a => StarSemiring a where
  star :: a -> a
  star x = one <+> plus x
  plus :: a -> a
  plus x = x <.> star x
```

Using this on types, you get:

```{.haskell}
star a = Either () (a, star a)
```

Which is just a standard list! Some pseudo-haskell on alternatives will give you:

```{.haskell}
star :: (Alternative f, Monoid a) => f a -> f a
star x = (x <.> star x) <+> pure mempty where
  (<.>) = liftA2 mappend
  (<+>) = <|>
```

Also known as [`many`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Control-Applicative.html#v:many). (although note that this breaks all the laws)

The $*$ for rationals is defined as:


$a* = \begin{cases}
  \frac{1}{1 - a} & \quad \text{if  } & 0 \leq a \lt 1, \\
  \infty          & \quad \text{if  } & a \geq 1.
\end{cases}$

[@droste_semirings_2009, p8]

So, combining the probability with the type-level business, the star of `Writer s a` is:

```{.haskell}
Either a (a, inverse of s, star (Writer s a))
```

Or, to put it another way: the `Odds`{.haskell} monad!

## Some Examples

So we've seen semirings for probabilities, maps, sets, etc. What else forms a semiring?

One of the most important applications (and a source of much of the notation) are regular expressions. In fact, the free semiring looks like a haskell datatype for regular expressions:

```{.haskell .literate}
data FreeStar a
 = Gen a
 | Zero
 | One
 | FreeStar a :<+> FreeStar a
 | FreeStar a :<.> FreeStar a
 | Star (FreeStar a)

instance Semiring (FreeStar a) where
  (<+>) = (:<+>)
  (<.>) = (:<.>)
  zero = Zero
  one = One
  
instance StarSemiring (FreeStar a) where
  star = Star
  
interpret :: StarSemiring s => (a -> s) -> FreeStar a -> s
interpret f = \case
  Gen x -> f x
  Zero -> zero
  One -> one
  l :<+> r -> interpret f l <+> interpret f r
  l :<.> r -> interpret f l <.> interpret f r
  Star x -> star (interpret f x)
```

This may be more efficiently encoded using the more initial approach. Using another semiring (near-semiring, specifically; and it requires the underlying monoid to be commutative):

```{.haskell .literate}
instance Monoid a => Semiring (Endo a) where
  Endo f <+> Endo g = Endo (\x -> f x <> g x)
  zero = Endo (const mempty)
  one = Endo id
  Endo f <.> Endo g = Endo (f . g)
  
instance (Monoid a, Eq a) => StarSemiring (Endo a) where
  star (Endo f) = Endo converge where
    converge x = x <> (if y == mempty then y else converge y) where
      y = f x
```

Then, interpreting the regex is as simple as writing an interpreter:

```{.haskell .literate}
asRegex :: Eq a => FreeStar (a -> Bool) -> [a] -> Bool
asRegex fs = any null . appEndo (interpret f fs) . pure where
  f p = Endo . mapMaybe $ \case
    (x:xs) | p x -> Just xs
    _ -> Nothing

char' :: Eq a => a -> FreeStar (a -> Bool)
char' c = Gen (c==)
```

Actually, you don't need the free version at all!

```{.haskell .literate}
runRegex :: Eq a => Endo [[a]] -> [a] -> Bool
runRegex fs = any null . appEndo fs . pure

char :: Eq a => a -> Endo [[a]]
char c = Endo . mapMaybe $ \case
  (x:xs) | c == x -> Just xs
  _ -> Nothing
  
instance IsString (Endo [String]) where
  fromString = mul . map char . reverse
  
(<^>) :: Semiring s => s -> s -> s
(<^>) = flip (<.>)

greet :: Endo [String]
greet = "H" <^> ("a" <+> "e") <^> "llo"
```
```{.haskell .literate .example .hidden_source}
:set -XOverloadedStrings
```
```{.haskell .literate .example}
runRegex greet "Hello"
True
```
```{.haskell .literate .example}
runRegex greet "Hallo"
True
```
```{.haskell .literate .example}
runRegex greet "Halo"
False
```

## Efficiency

Of course, that's about as slow as it gets when it comes to regexes. A faster representation is a [nondeterministic finite automaton](https://en.wikipedia.org/wiki/Nondeterministic_finite_automaton). This is a thing which has multiple states, and can transition between each state based on which character we receive. 

Each state is represented by something like a number. Alternatively, you can represent the state machine with a matrix, where each entry indicates whether or not that transition can occur. Actually, each entry can be an arbitrary semiring. So the whole thing is kind of like a map from indices to semirings (sound familiar?)

Taking some code from @dolan_fun_2013:

```{.haskell .literate}
data Matrix a = Scalar a
              | Matrix [[a]]
              
mjoin :: (Matrix a, Matrix a, Matrix a, Matrix a) -> Matrix a
mjoin (Matrix ws, Matrix xs, Matrix ys, Matrix zs) =
  Matrix ((zipWith (++) ws xs) ++ (zipWith (++) ys zs))
  
msplit :: Matrix a -> (Matrix a, Matrix a, Matrix a, Matrix a)
msplit (Matrix (row:rows)) = 
  (Matrix [[first]], Matrix [top]
  ,Matrix left,      Matrix rest )
  where
    (first:top) = row
    (left,rest) = unzip (map (\(x:xs) -> ([x],xs)) rows)
    
instance Semiring a => Semiring (Matrix a) where
  zero = Scalar zero
  one = Scalar one
  Scalar x <+> Scalar y = Scalar (x <+> y)
  Matrix x <+> Matrix y =
    Matrix (zipWith (zipWith (<+>)) x y)
  Scalar x <+> m = m <+> Scalar x
  Matrix [[x]] <+> Scalar y = Matrix [[x <+> y]]
  x <+> y = mjoin (first <+> y, top, left, rest <+> y)
    where (first, top, left, rest) = msplit x
  Scalar x <.> Scalar y = Scalar (x <.> y)
  Scalar x <.> Matrix y = Matrix ((map.map) (x<.>) y)
  Matrix x <.> Scalar y = Matrix ((map.map) (<.>y) x)
  Matrix x <.> Matrix y = 
    Matrix [ [ foldl1 (<+>) (zipWith (<.>) row col) | col <- cols ] 
           | row <- x ] where cols = transpose y

instance StarSemiring a => StarSemiring (Matrix a) where
  star (Matrix [[x]]) = Matrix [[star x]]
  star m = mjoin (first' <+> top' <.> rest' <.> left'
                 ,top' <.> rest', rest' <.> left', rest')
    where
      (first, top, left, rest) = msplit m
      first' = star first
      top' = first' <.> top
      left' = left <.> first'
      rest' = star (rest <+> left' <.> top)
```

## Modules.

permutations, replications.
Weighted parsers, regexes, natural lang, constraint programming

## References

[Permute](http://hackage.haskell.org/package/PermuteEffects-0.2/docs/Control-Permute.html)

[Replicate](http://hackage.haskell.org/package/ReplicateEffects-0.2/docs/Control-Replicate.html#t:Replicate)

