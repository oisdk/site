---
title: Semirings
tags: Haskell
bibliography: Semirings.bib
---
```{.haskell .literate .hidden_source}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms, ViewPatterns, LambdaCase #-}
{-# LANGUAGE RankNTypes, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists, MonadComprehensions #-}

module Semirings where

import qualified Data.Map.Strict as Map
import Data.Monoid
import Data.Foldable hiding (toList)
import Control.Applicative
import Control.Arrow (first)
import Control.Monad.Cont
import Data.Functor.Identity
import GHC.Exts
import Data.List hiding (insert)
```

I've been playing around a lot with semirings recently. A semiring is anything with addition, multiplication, zero and one. You can represent that in Haskell as:

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

I should note that what I'm calling a semiring here is often called a [rig](https://ncatlab.org/nlab/show/rig). I actually prefer the name "rig": a rig is a ring without **n**egatives (cute!); whereas a *semi*ring is a rig without neutral elements, which mirrors the definition of a semigroup. The nomenclature in this area is a mess, though (more on that later), so I went with the more commonly-used name for the sake of googleability.

At first glance, it looks quite numeric. Indeed, [PureScript](https://pursuit.purescript.org/packages/purescript-prelude/1.1.0/docs/Data.Semiring) uses it as the basis for its numeric hierarchy. (In my experience so far, it's nicer to use than Haskell's [`Num`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Prelude.html#t:Num))

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

However, there are far more types which can form a valid `Semiring`{.haskell} instance than can form a valid `Num`{.haskell} instance. For instance, the `negate`{.haskell} method on `Num`{.haskell} excludes types representing the natural numbers:

```{.haskell .literate}
newtype ChurchNat = ChurchNat { runNat :: forall a. (a -> a) -> a -> a}
 
data Nat = Zero | Succ Nat
```

These form perfectly sensible semirings, though:

```{.haskell .literate}
instance Semiring ChurchNat where
  zero = ChurchNat (const id)
  one = ChurchNat ($)
  ChurchNat n <+> ChurchNat m = ChurchNat (\f -> n f . m f)
  ChurchNat n <.> ChurchNat m = ChurchNat (n . m)

instance Semiring Nat where
  zero = Zero
  one = Succ Zero
  Zero <+> x = x
  Succ x <+> y = Succ (x <+> y)
  Zero <.> _ = Zero
  Succ Zero <.> x =x
  Succ x <.> y = y <+> (x <.> y)
```

The other missing method is `fromInteger`{.haskell}, which means decidedly non-numeric types are allowed:

```{.haskell .literate}
instance Semiring Bool where
  zero = False
  one  = True
  (<+>) = (||)
  (<.>) = (&&)
```

We can provide a more general definition of the [`Sum`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Monoid.html#t:Sum) and [`Product`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Monoid.html#t:Product) newtypes from [Data.Monoid](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Monoid.html#g:3):

```{.haskell .literate}
newtype Add a = Add
  { getAdd :: a
  } deriving (Eq, Ord, Read, Show, Semiring)

newtype Mul a = Mul
  { getMul :: a
  } deriving (Eq, Ord, Read, Show, Semiring)
```
```{.haskell .literate .hidden_source}
instance Functor Add where
  fmap f (Add x) = Add (f x)
instance Applicative Add where
  pure = Add
  Add f <*> Add x = Add (f x)
```

I'm using `Add`{.haskell} and `Mul`{.haskell} here to avoid name clashing.

```{.haskell .literate}
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

`add`{.haskell} and `mul`{.haskell} are equivalent to [`sum`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Foldable.html#v:sum) and [`product`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Foldable.html#v:product):

```{.haskell .literate .prop}
add xs == sum (xs :: [Integer])
```
```{.haskell .literate .prop}
mul xs == product (xs :: [Integer])
```

But they now work with a wider array of types: non-negative numbers, as we've seen, but specialised to `Bool`{.haskell} we get the familiar [`Any`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Monoid.html#t:Any) and [`All`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Monoid.html#t:All) newtypes (and their corresponding folds).

```{.haskell .literate .prop}
add xs == any id (xs :: [Bool])
```
```{.haskell .literate .prop}
mul xs == all id (xs :: [Bool])
```

So far, nothing amazing. We avoid a little bit of code duplication, that's all.

## A Semiring Map

In older versions of Python, [there was no native set type](https://www.python.org/dev/peps/pep-0218/). In its place, dictionaries were used, where the values would be booleans. In a similar fashion, before the [Counter](https://docs.python.org/2/library/collections.html#collections.Counter) type was added in 2.7, the traditional way of representing a multiset was using a dictionary where the values were integers.

Using semirings, both of these data structures can have the same type:

```{.haskell .literate}
newtype GeneralMap a b = GeneralMap
  { getMap :: Map.Map a b
  } deriving (Functor, Foldable, Show, Eq, Ord)
```

If operations are defined in terms of the `Semiring`{.haskell} class, the same code will work on a set *and* a multiset:

```{.haskell .literate}
insert :: (Ord a, Semiring b) => a -> GeneralMap a b -> GeneralMap a b
insert x = GeneralMap . Map.insertWith (<+>) x one . getMap

delete :: Ord a => a -> GeneralMap a b -> GeneralMap a b
delete x = GeneralMap . Map.delete x . getMap
```

How to get back the dictionary-like behaviour, then? Well, operations like `lookup`{.haskell} and `assoc`{.haskell} are better suited to a `Monoid`{.haskell} constraint, rather than `Semiring`{.haskell}:

```{.haskell .literate}
lookup :: (Ord a, Monoid b) => a -> GeneralMap a b -> b
lookup x = fold . Map.lookup x . getMap

assoc :: (Ord a, Applicative f, Monoid (f b)) 
      => a -> b -> GeneralMap a (f b) -> GeneralMap a (f b)
assoc k v = GeneralMap . Map.insertWith mappend k (pure v) . getMap
```

`lookup`{.haskell} is a function which should work on sets and multisets: however `Bool`{.haskell} and `Integer`{.haskell} don't have `Monoid`{.haskell} instances. To fix this, we can use the `Add`{.haskell} newtype from above. Now we have a decent interface for each of our data structures. It's helpful to think of each interpretation of the type like this:

```{.haskell .literate}
type Set      a   = GeneralMap a (Add Bool)
type MultiSet a   = GeneralMap a (Add Integer)
type Map      a b = GeneralMap a (First b)
type MultiMap a b = GeneralMap a [b]
```

Each of the functions from above specialises like this:

```{.haskell}
-- Set
insert :: Ord a => a -> Set a -> Set a
lookup :: Ord a => a -> Set a -> Add Bool
delete :: Ord a => a -> Set a -> Set a

-- MultiSet
insert :: Ord a => a -> MultiSet a -> MultiSet a
lookup :: Ord a => a -> MultiSet a -> Add Integer
delete :: Ord a => a -> MultiSet a -> MultiSet a

-- Map
assoc  :: Ord a => a -> b -> Map a b -> Map a b
lookup :: Ord a => a -> Map a b -> First b
delete :: Ord a => a -> Map a b -> Map a b

-- MultiMap
assoc  :: Ord a => a -> b -> MultiMap a b -> MultiMap a b
lookup :: Ord a => a -> MultiMap a b -> [b]
delete :: Ord a => a -> MultiMap a b -> MultiMap a b
```

This was actually where I first came across semirings: I was trying to avoid code duplication for a trie implementation. I wanted to get the Boom Hierarchy [@boom_further_1981] (plus maps) from the same underlying implementation.

It works *okay*. On the one hand, it's nice that you don't have to wrap the map type itself to get the different behaviour. There's only one `delete`{.haskell} function, which works on sets, maps, multisets, etc. I don't need to import the `TrieSet`{.haskell} module qualified, to differentiate between the *four* `delete`{.haskell} functions I've written.

The abstraction goes pretty far, also:

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
    
singleton :: Semiring b => a -> GeneralMap a b
singleton x = GeneralMap (Map.singleton x one)
```

On the other hand, some of the constraints aren't very nice. `Applicative`{.haskell} on the wrappers for the map and multimap, for instance. The fact that the lookup on sets and multisets returns a wrapped value is annoying. And I couldn't figure out a definition for `intersection`{.haskell}:

```{.haskell .literate}
intersection :: (Ord a, Semiring b)
             => GeneralMap a b -> GeneralMap a b -> GeneralMap a b
intersection (GeneralMap x) (GeneralMap y) =
  GeneralMap (Map.intersectionWith (<.>) x y)
```

While it works for sets, it doesn't make sense for multisets, and it doesn't work for maps. I couldn't find a more suitable semiring in order to represent what I wanted. (I'm probably after a different algebraic structure) 

## A Probability Semiring

While looking for a semiring to represent a valid intersection, I came across some other semirings. The *probability* semiring, for instance. It's just the normal semiring over the rationals, with a lower bound of 0, and an upper of 1.

It's useful in some cool ways. For instance, you could combine it with a list to get the probability monad [@erwig_functional_2006]. There's an example in PureScript's [Distributions](https://pursuit.purescript.org/packages/purescript-distributions/) package.

```{.haskell}
newtype Prob s a = Prob { runProb :: [(a,s)] }
```



This representation is unfortunately too slow to be useful (usually). In particular, there's a combinatorial explosion on every monadic bind. One of the strategies to reduce this explosion is to use a map:

```{.haskell}
newtype Prob s a = Prob { runProb :: Map.Map a s }
```

Because this doesn't allow duplicate keys, it will flatten the association list on every bind. Unfortunately, there's no huge efficiency gain, and in some cases an efficiency *loss* [@larsen_memory_2011]. Also, the `Ord`{.haskell} constraint on `a`{.haskell} prevents the above representation from conforming to `Monad`{.haskell}. (at least the standard version in the prelude)

Interestingly, this type is exactly the same as the `GeneralMap`{.haskell} from above. This is a theme I kept running into, actually: the `GeneralMap`{.haskell} type represents not just maps, multimaps, sets, multisets, but also a whole host of other data structures.

## Cont

Edward Kmett had an interesting blog post about "Free Modules and Functional Linear Functionals" [-@kmett_modules_2011]. In it, he talked about this type:

```{.haskell}
infixr 0 $*
newtype Linear r a = Linear { ($*) :: (a -> r) -> r }
```

Also known as [`Cont`{.haskell}](https://hackage.haskell.org/package/mtl-2.2.1/docs/Control-Monad-Cont.html#t:Cont), the continuation monad. What's interesting about the above type is that it can encode the probability monad:

```{.haskell .literate}
fromProbs :: (Semiring s, Applicative m) => [(a,s)] -> ContT s m a
fromProbs xs = ContT $ \k ->
  foldr (\(x,s) a -> liftA2 (<+>) (fmap (s<.>) (k x)) a) (pure zero) xs

probOfT :: (Semiring r, Applicative m) => (a -> Bool) -> ContT r m a -> m r
probOfT e c = runContT c (\x -> if e x then pure one else pure zero)

probOf :: Semiring r => (a -> Bool) -> Cont r a -> r
probOf e = runIdentity . probOfT e

uniform :: Applicative m => [a] -> ContT Double m a
uniform xs =
  let s = 1.0 / fromIntegral (length xs)
  in fromProbs (map (flip (,) s) xs)
```

Multiplication isn't paid for on every bind, making this (potentially) a more efficient implementation than both the map and the association list.
  
You can actually make the whole thing a semiring:

```{.haskell .literate}
instance (Semiring r, Applicative m) => Semiring (ContT r m a) where
  one  = ContT (const (pure one))
  zero = ContT (const (pure one))
  f <+> g = ContT (\k -> liftA2 (<+>) (runContT f k) (runContT g k))
  f <.> g = ContT (\k -> liftA2 (<.>) (runContT f k) (runContT g k))
```

Which gives you a lovely `Alternative`{.haskell} instance:

```{.haskell .literate}
instance (Semiring r, Applicative m) => Alternative (ContT r m) where
  (<|>) = (<+>)
  empty = zero
```

The multiplication here is equivalent to the unsatisfactory intersection from above. Zero is the empty map, one is the map where *every* key has a value of one. To make one in the previous implementations, you would have to enumerate over every possible value for the keys. In this version, to *inspect* the values you have to enumerate over every possible key.

I think I now have a name for the probability monad / general map / Cont thing: a *covector*.

I think that the transformer version of Cont has a valid interpretation, also. If I ever understand @hirschowitz_modules_2010 I'll put it into a later follow-up post.

## Conditional choice

As a short digression, you can beef up the `<|>`{.haskell} operator a little, with something like [the conditional choice operator](http://zenzike.com/posts/2011-08-01-the-conditional-choice-operator):

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

Interestingly, the probability monad can be constructed from more primitive types. For instance, extracting the `WriterT`{.haskell} monad transformer gives you:

```{.haskell}
WriterT (Product Double) []
```

Eric Kidd describes it as `PerhapsT`{.haskell}: a `Maybe`{.haskell} with attached probability in his [excellent blog post](http://www.randomhacks.net/2007/02/21/refactoring-probability-distributions/) [and his paper in -@kidd_build_2007].

Straight away, we can optimise this representation by transforming [leaky](https://twitter.com/gabrielg439/status/659170544038707201) `WriterT`{.haskell} into a state monad:

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

I'm not sure yet, but I think this might have something to do with the isomorphism between `Cont ((->) s)`{.haskell} and `State s` [@kmett_free_2011].

You can even make it look like a normal (non-transformer) writer with some pattern synonyms:

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

Looking back at Cont, it is reminiscent of a particular encoding of the free monoid from @doel_free_2015:

```{.haskell}
newtype FreeMonoid a = FreeMonoid
  { forall m. Monoid m => (a -> m) -> m }
```

So possibly covectors represent the free semiring, in some way.

Another encoding which looks free-ish is another efficient implementation of the probability monad from @larsen_memory_2011:

```{.haskell}
data Dist a where
  Certainly :: a -> Dist a -- only possible value
  Choice :: Probability -> Dist a -> Dist a -> Dist a
  Fmap :: (a -> b) -> Dist a -> Dist b
  Join :: Dist (Dist a) -> Dist a
```

This looks an awful lot like a weighted [free alternative](https://hackage.haskell.org/package/free-4.12.4/docs/Control-Alternative-Free.html). Is it a free semiring, then?

Maybe. There's a parallel between the relationship between monoids and semirings and applicatives and [`Alternative`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Control-Applicative.html#t:Alternative)s [@rivas_monoids_2015]. In a way, where monads are monoids in the category of endofunctors, alternatives are *semirings* in the category of endofunctors.

This parallel probably isn't as consistent as I first thought. First of all, the above paper uses near-semirings, not semirings. A near-semiring is a semiring where the requirements for left distribution of multiplication over addition and commutative addition are dropped. Secondly, the class which most mirrors near-semirings is [`MonadPlus`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Control-Monad.html#t:MonadPlus), not alternative. (alternative doesn't have annihilation) Thirdly, right distribution of multiplication over addition *isn't* required `MonadPlus`{.haskell}: it's a further law required on top of the existing laws. Fourthly, most types in the Haskell ecosystem today which conform to `MonadPlus`{.haskell} *don't* conform to this extra law: in fact, those that do seem to be lists of some kind or another.

Another class is probably needed on top of the two already there, called `Nondet`{.haskell} by @fischer_reinventing_2009.

An actual free near-semiring looks like this:

```{.haskell}
data Free f x = Free { unFree :: [FFree f x] }
data FFree f x = Pure x | Con (f (Free f x))
```

Specialised to the `Identity`{.haskell} monad, that becomes:

```{.haskell}
data Forest a = Forest { unForest :: [Tree x] }
data Tree x = Leaf x | Branch (Forest x)
```

De-specialised to the [free monad transformer](https://hackage.haskell.org/package/free-4.12.4/docs/Control-Monad-Trans-Free.html), it becomes:

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

Does the [odds monad](/posts/2016-09-27-odds-lhs.html) fit in to any of this?

While `WriterT (Product Rational) []`{.haskell} is a valid definition of the traditional probability monad, it's *not* the same as the odds monad. If you take the odds monad, and parameterize it over the weight of the tail, you get this:

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

Types in haskell also form a semiring.

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

The $*$ for rationals is defined as [@droste_semirings_2009, p8]:

$a* = \begin{cases}
  \frac{1}{1 - a} & \quad \text{if  } & 0 \leq a \lt 1, \\
  \infty          & \quad \text{if  } & a \geq 1.
\end{cases}$

So, combining the probability with the type-level business, the star of `Writer s a` is:

```{.haskell}
Either (1, a) (a, s / (1 - s), star (Writer s a))
```

Or, to put it another way: the odds monad!

## Some Examples

So we've seen semirings for probabilities, maps, sets, etc. What else forms a semiring?

One of the most important applications (and a source of much of the notation) is regular expressions. In fact, the free semiring looks like a haskell datatype for regular expressions:

```{.haskell .literate}
data FreeStar a
 = Gen a
 | Zer
 | One
 | FreeStar a :<+> FreeStar a
 | FreeStar a :<.> FreeStar a
 | Star (FreeStar a)

instance Semiring (FreeStar a) where
  (<+>) = (:<+>)
  (<.>) = (:<.>)
  zero = Zer
  one = One
  
instance StarSemiring (FreeStar a) where
  star = Star
  
interpret :: StarSemiring s => (a -> s) -> FreeStar a -> s
interpret f = \case
  Gen x -> f x
  Zer -> zero
  One -> one
  l :<+> r -> interpret f l <+> interpret f r
  l :<.> r -> interpret f l <.> interpret f r
  Star x -> star (interpret f x)
```

Using another semiring (near-semiring, specifically; and it requires the underlying monoid to be commutative):

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
```

With some `-XOverloadedStrings`{.haskell} magic, you get a pretty nice interface:

```{.haskell .literate}
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

Of course, that's about as slow as it gets when it comes to regexes. A faster representation is a [nondeterministic finite automaton](https://swtch.com/~rsc/regexp/regexp1.html). One such implementation in haskell is [Gabriel Gonzalez's](https://github.com/Gabriel439/slides/blob/master/regex/regex.md).

The regex type in that example can be immediately made to conform to `Semiring`{.haskell} and `StarSemiring`{.haskell}. However, it might be more interesting to translate the *implementation* into using semirings. The type of a regex looks like this:

```{.haskell}
type State = Int

{ _startingStates         :: Set State
, _transitionFunction     :: Char -> State -> Set State
, _acceptingStates        :: Set State }
```

As you might note, the set data structure can be reformulated as a map from states to some semiring. In fact, the whole code can be translated into using some arbitrary semiring pretty readily:

```{.haskell .literate}
type State = Int

data Regex i s = Regex
  { _numberOfStates     :: Int 
  , _startingStates     :: GeneralMap State s
  , _transitionFunction :: i -> State -> GeneralMap State s
  , _acceptingStates    :: GeneralMap State s }

isEnd :: Semiring s => Regex i s -> s
isEnd (Regex _ as _ bs) = add (intersection as bs)

match :: Regex Char (Add Bool) -> String -> Bool
match r = getAdd . isEnd . foldl' run r where
  run (Regex n (GeneralMap as) f bs) i = Regex n as' f bs
    where as' = mconcat [ fmap (v<.>) (f i k)  | (k,v) <- Map.assocs as ]


satisfy :: Semiring s => (i -> s) -> Regex i (Add s)
satisfy predicate = Regex 2 as f bs
  where
    as = singleton 0
    bs = singleton 1

    f i 0 = assoc 1 (predicate i) mempty
    f _ _ = mempty

once :: Eq i => i -> Regex i (Add Bool)
once x = satisfy (== x)

shift :: Int -> GeneralMap State s -> GeneralMap State s
shift n = GeneralMap . Map.fromAscList . (map.first) (+ n) . Map.toAscList . getMap

instance (Semiring s, Monoid s) => Semiring (Regex i s) where

  one = Regex 1 (singleton 0) (\_ _ -> mempty) (singleton 0)
  zero = Regex 0 mempty (\_ _ -> mempty) mempty

  Regex nL asL fL bsL <+> Regex nR asR fR bsR = Regex n as f bs
    where
      n  = nL + nR
      as = mappend asL (shift nL asR)
      bs = mappend bsL (shift nL bsR)
      f i s | s < nL    = fL i s
            | otherwise = shift nL (fR i (s - nL))

  Regex nL asL fL bsL <.> Regex nR asR fR bsR = Regex n as f bs where

    n = nL + nR

    as = let ss = add (intersection asL bsL)
         in mappend asL (fmap (ss<.>) (shift nL asR))

    f i s =
        if s < nL
        then let ss = add (intersection r bsL)
             in mappend r (fmap (ss<.>) (shift nL asR))
        else shift nL (fR i (s - nL))
      where
        r = fL i s
    bs = shift nL bsR

instance (StarSemiring s, Monoid s) => StarSemiring (Regex i s) where
  star (Regex n as f bs) = Regex n as f' as
    where
      f' i s =
          let r = f i s
              ss = add (intersection r bs)
          in mappend r (fmap (ss<.>) as)

  plus (Regex n as f bs) = Regex n as f' bs
    where
      f' i s =
          let r = f i s
              ss = add (intersection r bs)
          in mappend r (fmap (ss<.>) as)


instance IsString (Regex Char (Add Bool)) where
  fromString = mul . map once
```

This begins to show some of the real power of using semirings and covectors. We have a normal regular expression implementation when we use the covector over bools. Use the probability semiring, and you've got probabilistic parsing. Instead of a map, if you use an integer (each bit being a value, the keys being the bit position), you have a super-fast implementation (and the final implementation used in the original example).

Swap in the [tropical semiring](https://ncatlab.org/nlab/show/max-plus+algebra): a semiring over the reals where addition is the max function, and multiplication is addition of reals. Now you've got a depth-first parser.

That's how you might swap in different interpretations. How about swapping in different *implementations*? Well, there might be some use to swapping in the [CYK algorithm](https://en.wikipedia.org/wiki/CYK_algorithm), or the Gauss-Jordan-Floyd-Warshall-McNaughton-Yamada algorithm [@oconnor_very_2011]. You can use these in combination with a different representation of the underlying data structure: a matrix.

## Square Matrices

A square matrix can represent your function from input states to output states. Take, for instance, a regular expression with three possible states. Its state transfer function might look like this:

$transfer = \begin{cases}
1 \quad & \{ 2, 3 \} \\
2 \quad & \{ 1 \} \\
3 \quad & \emptyset
\end{cases}$

It has the type of:

```{.haskell}
State -> Set State
```

Where `State`{.haskell} is an integer. You can represent the set as a vector, where each position is a key, and each value is whether or not that key is present:

$transfer = \begin{cases}
1 \quad & \begin{array} ( 0 & 1 & 1 ) \end{array} \\
2 \quad & \begin{array} ( 1 & 0 & 0 ) \end{array} \\
3 \quad & \begin{array} ( 0 & 0 & 0 ) \end{array}
\end{cases}$

Then, the matrix representation is obvious:

$transfer = \left( \begin{array}{ccc}
0 & 1 & 1 \\
1 & 0 & 0 \\
0 & 0 & 0 \end{array} \right)$

This is the semiring of square matrices. It is, of course, yet *another* covector. The "keys" are the transfers: `1 -> 2`{.haskell} or `2 -> 3`{.haskell}, represented by the indices of the matrix. The "values" are whether or not that transfer is permitted.

The algorithms for the usual semiring operations on matrices like this are well-known and well-optimized. I haven't yet fiddled around with them Haskell, so I don't know how fast they can be. For now, though, there's an elegant list-based implementation in @dolan_fun_2013:

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

## Permutation parsing

A lot of the use from semirings comes from "attaching" them to other values. Attaching a semiring to effects (in the form of an applicative) can give you *repetition* of those effects. The excellent [ReplicateEffects](http://hackage.haskell.org/package/ReplicateEffects) library explores this concept in depth.

It's based on this type:

```{.haskell}
data Replicate a b
  = Nil
  | Cons (Maybe b) (Replicate a (a -> b))
```

This type can be made to conform to `Semiring`{.haskell} (and `Starsemiring`{.haskell}, etc) trivially.

In the simplest case, it has the same behaviour as [`replicateM`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Control-Monad.html#v:replicateM). Even the more complex combinators, like `atLeast`{.haskell}, can be built on `Alternative`{.haskell}:

```{.haskell}
atLeast :: Alternative f => Int -> f a -> f [a]
atLeast m f = go (max 0 m) where
  go 0 = many f
  go n = liftA2 (:) f (go (n-1))
  
atMost :: Alternative f => Int -> f a -> f [a]
atMost m f = go (max 0 m) where
  go 0 = pure []
  go n = liftA2 (:) f (go (n-1)) <|> pure []
```

There are two main benefits over using the standard alternative implementation. First, you can choose greedy or lazy evaluation of the effects *after* the replication is built.

Secondly, the *order* of the effects doesn't have to be specified. This allows you to execute permutations of the effects, in a permutation parser, for instance. The permutation is totally decoupled from the declaration of the repetition (it's in a totally separate library, in fact: [PermuteEffects](http://hackage.haskell.org/package/PermuteEffects)). Its construction is reminiscent of the [free alternative](https://hackage.haskell.org/package/free-4.12.4/docs/Control-Alternative-Free.html#t:AltF).

Having the replicate type conform to `Semiring`{.haskell} is all well and good: what I'm interested in is seeing if its implementation is another semiring-based object in disguise. I'll revisit this in another post.

## Algebraic Search

List comprehension notation is one of my all-time favourite bits of syntactic sugar. It seems almost *too* declarative to have a reasonable implementation strategy. The vast majority of the time, it actually works in a sensible way. There are exceptions, though. Take a reasonable definition of a list of Pythagorean triples:

```{.haskell}
[ (x,y,z) | x <- [1..], y <- [1..], z <- [1..], x*x + y*y == z*z ]
```

The above expression will diverge. It will search through every possible value for `z`{.haskell} before incrementing either `x`{.haskell} or `y`{.haskell}. Since there are infinite values for `z`{.haskell}, it will never find a triple. For search problems like the above, a list comprehension is equivalent to depth-first search. 

In order to express another kind of search (either breadth-first or depth-bounded), a different monad is needed. These monads explored in @fischer_reinventing_2009 and @spivey_algebras_2009.

You can actually use the *exact* same notation as above with another monad using `-XMonadComprehensions`{.haskell} and `-XOverloadedLists`{.haskell}.

```{.haskell .literate}
trips :: ( Alternative m
         , Monad m
         , IsList (m Integer)
         , Enum (Item (m Integer))
         , Num (Item (m Integer)))
      => m (Integer,Integer,Integer)
trips = [ (x,y,z) | x <- [1..], y <- [1..], z <- [1..], x*x + y*y == z*z ]
```

So then, here's the challenge: swap in different `m`{.haskell}s via a type annotation, and prevent the above expression from diverging.

As one example, here's some code adapted from @fischer_reinventing_2009:

```{.haskell .literate}
instance (Monoid r, Applicative m) => Monoid (ContT r m a) where
  mempty = ContT (const (pure mempty))
  mappend (ContT f) (ContT g) = ContT (\x -> liftA2 mappend (f x) (g x))
  
newtype List a = List { runList :: forall m. Monoid m => Cont m a } deriving Functor

instance Foldable List where foldMap = flip (runCont.runList)
  
instance Show a => Show (List a) where show = show . foldr (:) []

instance Monoid (List a) where
  mappend (List x) (List y) = List (mappend x y)
  mempty = List mempty
  
instance Monoid a => Semiring (List a) where
  zero = mempty
  (<+>) = mappend
  (<.>) = liftA2 mappend
  one = pure mempty

bfs :: List a -> [a]
bfs = toList . fold . levels . anyOf

newtype Levels a = Levels { levels :: [List a] } deriving Functor

instance Applicative Levels where
  pure x = Levels [pure x]
  Levels fs <*> Levels xs = Levels [ f <*> x | f <- fs, x <- xs ]
  
instance Alternative Levels where
  empty = Levels []
  Levels x <|> Levels y = Levels (mempty : merge x y)

instance IsList (List a) where
  type Item (List a) = a
  fromList = anyOf
  toList = foldr (:) []
  
instance Applicative List where
  pure x = List (pure x)
  (<*>) = ap

instance Alternative List where
  empty = mempty
  (<|>) = mappend

instance Monad List where
  x >>= f = foldMap f x

anyOf :: (Alternative m, Foldable f) => f a -> m a
anyOf = getAlt . foldMap (Alt . pure)

merge :: [List a] -> [List a] -> [List a]
merge []      ys    = ys
merge xs      []    = xs
merge (x:xs) (y:ys) = mappend x y : merge xs ys
```
```{.haskell .literate .example}
take 3 (bfs trips)
[(3,4,5),(4,3,5),(6,8,10)]
```

The only relevance to semirings is the merge function. The semiring over lists is the semiring over polynomials:

```{.haskell .literate}
instance Semiring a => Semiring [a] where
  one = [one]
  zero = []
  [] <+> ys = ys
  xs <+> [] = xs
  (x:xs) <+> (y:ys) = (x <+> y) : (xs <+> ys)
  [] <.> _ = []
  _ <.> [] = []
  (x:xs) <.> (y:ys) =
    (x <.> y) : (map (x <.>) ys <+> map (<.> y) xs <+> (xs <.> ys))
```

The `<+>`{.haskell} is the same as the `merge`{.haskell} function. I think the `<.>`{.haskell} might be a more valid definition of the `<*>`{.haskell} function, also.

```{.haskell}
instance Applicative Levels where
  pure x = Levels [pure x]
  Levels [] <*> _ = Levels []
  _ <*> Levels [] = Levels []
  Levels (f:fs) <*> Levels (x:xs) = Levels $
    (f <*> x) : levels (Levels (fmap (f <*>) xs) 
             <|> Levels (fmap (<*> x) fs)
             <|> (Levels fs <*> Levels xs))
```

## Conclusion

I've only scratched the surface of this abstraction. There are several other interesting semirings: polynomials, logs, Viterbi, Łukasiewicz, languages, multisets, bidirectional parsers, etc. Hopefully I'll eventually be able to put this stuff into a library or something. In the meantime, I definitely will write some posts on the application to context-free parsing, bidirectional parsing (I just read @breitner_showcasing_2016) and search. 

## References
