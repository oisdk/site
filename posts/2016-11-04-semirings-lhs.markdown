---
title: Semirings
tags: Haskell
bibliography: Semirings.bib
---
```{.haskell .literate .hidden_source}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms, ViewPatterns #-}

module Semirings where

import qualified Data.Map.Strict as Map
import Data.Monoid
import Data.Foldable
import Data.Ratio
import Control.Applicative
import Control.Arrow (first)
```

I've been playing around a lot with [semirings](https://en.wikipedia.org/wiki/Semiring) recently. Here's what it looks like:

```{.haskell .literate}
class Semiring a where
  zero :: a
  one :: a
  infixl 7 <.>
  (<.>) :: a -> a -> a
  infixl 6 <+>
  (<+>) :: a -> a -> a
```

It's kind of like a combination of two  [`Monoid`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Data-Monoid.html)s. It's got the normal monoid laws on `<+>`{.haskell} and `<.>`{.haskell}, with a couple extras:

* Commutivity of `<+>`{.haskell}:

```{.haskell}
x <+> y = y <+> x
```

* Distribution of `<.>`{.haskell} over `<+>`{.haskell}, right and left:

```{.haskell}
x <.> (y <+> z) = (x <.> y) <+> (x <.> z)
(x <+> y) <.> z = (x <.> z) <+> (y <.> z)
zero <.> a = a <.> zero = zero
```

At first glance, it looks quite numeric. Indeed, [PureScript](https://pursuit.purescript.org/packages/purescript-prelude/1.1.0/docs/Data.Semiring) uses it as the basis for its numeric hierarchy. It certainly works a lot nicer than Haskell's [`Num`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Prelude.html#g:5).

```{.haskell .literate}
instance Semiring Integer where
  zero = 0
  one = 1
  (<+>) = (+)
  (<.>) = (*)
```

However, `Bool`{.haskell} also conforms:

```{.haskell .literate}
instance Semiring Bool where
  zero = False
  one = True
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

I got using semirings first to try and avoid code duplication for a trie implementation. Basically, I wanted to be able to write one map-like type, and decide whether it was a set, map, multimap, multiset, etc. based on types. (and avoiding `newtype`{.haskell}s as much as possible) `Monoid`{.haskell}s worked for a while:

```{.haskell .literate}
newtype GeneralMap a b = GeneralMap
  { getMap :: Map.Map a b
  } deriving (Functor, Show, Eq, Ord)

lookup :: (Ord a, Monoid b) => a -> GeneralMap a b -> b
lookup x = fold . Map.lookup x . getMap

assoc :: (Ord a, Applicative f, Monoid (f b)) => a -> b -> GeneralMap a (f b) -> GeneralMap a (f b)
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

fromAssocs :: (Ord a, Applicative f, Monoid (f b), Foldable t) => t (a, b) -> GeneralMap a (f b)
fromAssocs = foldr (uncurry assoc) (GeneralMap Map.empty)

instance (Ord a, Monoid b) => Monoid (GeneralMap a b) where
  mempty = GeneralMap Map.empty
  mappend (GeneralMap x) (GeneralMap y) = GeneralMap (Map.unionWith mappend x y)
```

That's about as far as I got, though. In particular, intersection wasn't very easy to define:

```{.haskell .literate}
intersection :: (Ord a, Semiring b) => GeneralMap a b -> GeneralMap a b -> GeneralMap a b
intersection (GeneralMap x) (GeneralMap y) = GeneralMap (Map.intersectionWith (<.>) x y)
```

While it works for `Set`s, it doesn't make sense for `MultiSet`s, and it doesn't work for `Map`s. I couldn't find a more suitable semiring in order to represent what I wanted. (I'm probably after a different algebraic structure) 

## A Probability Semiring

While searching, though, I came across some other interesting semirings. The *Probability* semiring, in particular, was pretty interesting. It's just the normal semiring over the rationals, with a lower bound of 0, and an upper of 1. You could combine it with a list to get the traditional probability monad: there's an example in PureScript's [Distributions](https://pursuit.purescript.org/packages/purescript-distributions/) package.

As it turns out, you can build the probability monad out of smaller transformers:

```{.haskell}
WriterT (Product Double) []
```

[Eric Kidd describes it as `PerhapsT`{.haskell}: a `Maybe`{.haskell} with attached probability in this excellent blog post](http://www.randomhacks.net/2007/02/21/refactoring-probability-distributions/).

Using a semiring, the same can be expressed like this:

```{.haskell}
WriterT (Mul Double) []
```

That's got an extra `newtype`{.haskell}, though, which reduces the power of the semigroup. Let's make a whole new monad transformer:

```{.haskell .literate}
newtype WeightedT s m a = WeightedT
  { getWeightedT :: m (s, a) 
  } deriving (Functor, Foldable, Traversable)
```

It can conform to the traditional typeclasses using some help from the [prelude-extras](https://hackage.haskell.org/package/prelude-extras) package:
```{.haskell .literate .hidden_source}
class Eq1 f where
  (==#) :: Eq a => f a -> f a -> Bool

class Eq1 f => Ord1 f where
  compare1 :: Ord a => f a -> f a -> Ordering

class Show1 f where
  showsPrec1 :: Show a => Int -> f a -> ShowS

instance Eq1 [] where (==#) = (==)
instance Ord1 [] where compare1 = compare
instance Show1 [] where showsPrec1 = showsPrec
```
```{.haskell .literate}
instance (Eq1 m, Eq s, Eq a) => Eq (WeightedT s m a) where
  WeightedT x == WeightedT y = x ==# y

instance (Ord1 m, Ord s, Ord a) => Ord (WeightedT s m a) where
  compare (WeightedT x) (WeightedT y) = compare1 x y

instance (Show1 m, Show s, Show a) => Show (WeightedT s m a) where
  showsPrec n (WeightedT x) =
    showParen (n >= 10)
      $ showString "WeightedT {getWeightedT = "
      . showsPrec1 0 x
      . showChar '}'
```

And the `Monad`{.haskell} instances are similar to `WriterT`{.haskell}:

```{.haskell .literate}
pairwise :: (afst -> bfst -> cfst)
         -> (asnd -> bsnd -> csnd)
         -> (afst,asnd)
         -> (bfst,bsnd)
         -> (cfst,csnd)
pairwise f g ~(w,x) ~(y,z) = (f w y, g x z)

liftA2T :: Applicative f
        => (afst -> bfst -> cfst)
        -> (asnd -> bsnd -> csnd)
        -> f (afst,asnd)
        -> f (bfst,bsnd)
        -> f (cfst,csnd)
liftA2T f g = liftA2 (pairwise f g)

instance (Applicative m, Semiring s) => Applicative (WeightedT s m) where
  pure x = WeightedT (pure (one,x))
  WeightedT fs <*> WeightedT xs = WeightedT (liftA2T (<.>) ($) fs xs)

instance (Monad m, Semiring s) => Monad (WeightedT s m) where
  WeightedT xs >>= f =
    WeightedT ((\(p,x) -> (fmap.first.(<.>)) p (getWeightedT (f x))) =<< xs)
```

It's the same as `WriterT`{.haskell} so far (with a different monoid). You can even make it an instance of the `MonadWriter`{.haskell} class:

```{.haskell}
instance (Monad m, Semiring s) => MonadWriter (Mul s) (WeightedT s m)
```

The first obvious advantage to the semiring is that the function for calculating probability can be defined directly:

```{.haskell .literate}
instance (Semiring a, Semiring b) => Semiring (a,b) where
        zero = (zero, zero)
        (a1,b1) <+> (a2,b2) =
                (a1 <+> a2, b1 <+> b2)
        one = (one, one)
        (a1,b1) <.> (a2,b2) =
                (a1 <.> a2, b1 <.> b2)

probOf :: (Semiring s, Foldable f)
       => (a -> Bool)
       -> WeightedT s f a
       -> (s,s)
probOf e = getAdd . foldMap (uncurry f) . getWeightedT where
  f p x = Add (if e x then p else zero, p)

uniform :: Semiring s => [a] -> WeightedT s [] a
uniform xs = WeightedT (map ((,) one) xs)

die :: WeightedT Integer [] Integer
die = uniform [1..6]
```
```{.haskell .literate .example}
probOf (6==) ((+) <$> die <*> die)
(5,36)
```

The other advantage is that you get an interesting `Alternative`{.haskell} instance:

```{.haskell .literate}
instance (Semiring s, Alternative m, Foldable m) => Alternative (WeightedT s m) where
  empty = WeightedT empty
  WeightedT xs <|> WeightedT ys = WeightedT $
    (fmap.first.(<.>)) yssum xs <|> (fmap.first.(<.>)) xssum ys where
      pssum = getAdd . foldMap (Add . fst)
      xssum = pssum xs
      yssum = pssum ys
```

This almost certainly breaks all sorts of rules. This makes things involving choice make much more sense:

```{.haskell .literate .example}
probOf (1==) (uniform [1] <|> uniform [2,3,4])
(3,6)
```

Other combinators, like `mfilter`{.haskell}, also work.

All of this is still incredibly slow, obviously. One issue is to do with [`WriterT` leaking](https://twitter.com/gabrielg439/status/659170544038707201). (although it's by no means the only problem) The solution is to reformulate `WeightedT`{.haskell} as a State monad:

```{.haskell .literate}
newtype WeightedT' s m a = WeightedT' 
  { getWeightedT' :: s -> m (s, a)
  } deriving Functor
  
instance Monad m => Applicative (WeightedT' s m) where
  pure x = WeightedT' $ \s -> pure (s,x)
  WeightedT' fs <*> WeightedT' xs = WeightedT' $ \s -> do
    (p, f) <- fs s
    (t, x) <- xs p
    pure (t, f x)
  
instance Monad m => Monad (WeightedT' s m) where
  WeightedT' x >>= f = WeightedT' $ \s -> do
    (p, x) <- x s
    getWeightedT' (f x) p
```

You can even make it look like a normal (non-transformer) writer with some pattern synonyms:

```{.haskell .literate .hidden_source}
newtype Identity a = Identity { runIdentity :: a }
```
```{.haskell .literate}
pattern Weighted w <- (runIdentity . flip getWeightedT' zero -> w) where
  Weighted (w,x) = WeightedT' (\s -> Identity (s <.> w, x) )
```

## Free

How about the other plays on probability? `Odds`{.haskell}, the odds-tree, etc.?

If you take out the writer part of the monad for each, you're left with something like this:

```{.haskell}
data Odds m a = Certain a | Choice (m (a, Odds a)) -- Odds-list
data Odds m a = Certain a | Choice (m (a,a))       -- Odds-tree
```

The first thing that comes to mind is [`ListT`{.haskell} done right](https://wiki.haskell.org/ListT_done_right):

```{.haskell .literate}
newtype ListT m a = ListT { next :: m (Step m a) }
data Step m a = Cons a (ListT m a) | Nil
```

(I'm using [Gabriel Gonzalez](http://www.haskellforall.com/2016/07/list-transformer-beginner-friendly-listt.html)'s version here)

It's *kind* of like the traditional probability monad is:

```{.haskell}
WriterT (Product Rational) []
```

Whereas the odds-based variant is:

```{.haskell}
ListT (Weighted Rational)
```

Except that `ListT`{.haskell} admits empty lists, which I don't want.

Another option is the [Cofree Comonad](https://hackage.haskell.org/package/free-4.12.4/docs/Control-Comonad-Cofree.html):

```{.haskell .literate}
data Cofree f a = a :< (f (Cofree f a))
```

You can make a non-empty list with:

```{.haskell .literate}
type NonEmpty = Cofree Maybe
```

So you could also make the odds monad with:

```{.haskell .literate}
type Odds = Cofree (WeightedT Rational Maybe)
```

Interestingly, `WeightedT Rational Maybe`{.haskell} is basically [`PerhapsT`{.haskell}](http://www.randomhacks.net/2007/02/21/refactoring-probability-distributions/), as was mentioned earlier.

And the tree? Well, adding the [free monad](https://hackage.haskell.org/package/free-4.12.4/docs/Control-Monad-Free.html#t:Free):

```{.haskell .literate}
data Free f a = Pure a | Free (f (Free f a))
```

To a pair:

```{.haskell .literate}
data Pair a = Pair a a
```

You get a type like:

```{.haskell .literate}
data Tree a = Bin (Tree a) (Tree a) | Tip a
```

(This is the example given for the [`MonadFree`{.haskell} class](https://hackage.haskell.org/package/free-4.12.4/docs/Control-Monad-Free.html#t:MonadFree)).

So the Choice-tree is something like the free monad over:

```{.haskell .literate}
data WeightedChoice s a = WeightedChoice a s a deriving Show
```

This type is kind of interesting, I think. It's like a datatype for branching. You can make it nicer to construct with [the conditional choice operator](http://zenzike.com/posts/2011-08-01-the-conditional-choice-operator):

```{.haskell .literate}
data WeightedChoice s a = WeightedChoice
  { left :: a
  , right :: a
  , ratioLeftToRight :: s
  } deriving Show

(|>) :: s -> a -> a -> WeightedChoice s a
(p |> r) l = WeightedChoice l r p

(<|) :: a -> (a -> WeightedChoice s a) -> WeightedChoice s a
l <| r = r l

infixr 0 <|
infixr 0 |>
```

```{.haskell .literate .example}
'a' <| 0.3 |> 'b'
WeightedChoice {left = 'a', right = 'b', ratioLeftToRight = 0.3}
```

Or even:

```{.haskell .literate .example}
'a' <| 1  %  2 |> 'b'
WeightedChoice {left = 'a', right = 'b', ratioLeftToRight = 1 % 2}
```

The shape of that operator hints strongly at `<|>`{.haskell} from the [Alternative](https://hackage.haskell.org/package/base-4.9.0.0/docs/Control-Applicative.html#t:Alternative) class. So does the free alternative fit in here somewhere?

Unfortunately not, it [looks like](https://hackage.haskell.org/package/free-4.12.4/docs/Control-Alternative-Free.html):

```{.haskell .literate}
newtype Alt	 = Alt
  { alternatives :: [AltF f a] }
  
data AltF f a where
  Ap     :: f a -> Alt f (a -> b) -> AltF f b
  Pure   :: a                     -> AltF f a
```

## Everything is a semiring

Looking at these very general representations, I came across the paper by @rivas_monoids_2015. It explores the similarity between semirings (or near-semirings) and a whole bunch of other things.

If you think of a semiring as something which is a monoid in two ways, there are some analogs:

```{.haskell}
instance Semiring Monad where
  (<.>) = (>>=)
  one = pure  -- Monoid in the category of endofunctors!
  
  (<+>) = mplus
  zero = mzero

instance Semiring Applicative where
  (<.>) = (<*>)
  one = pure
  
  (<+>) = (<|>)
  zero = empty
  
instance Semiring OtherApplicative where
  (<.>) = (<*>)
  one = pure
  
  (<+>) = other (<*>) -- ie ZipList, etc
  zero = other pure
  
instance Semiring Arrow where
  (<.>) = (***)
  one = arr id
  
  (<+>) = (|||)
  zero = left id
```

However, as [Edward Kmett points out](https://www.reddit.com/r/haskell/comments/3dlz6b/from_monoids_to_nearsemirings_the_essence_of/ct6mr0g/), these similarities aren't necessarily that consistent.


There's even a similarity with types:

```{.haskell}
(<.>) = (,)
one = ()

(<+>) = Either
zero = Void
```

There's an extra you can add to semirings: [Star semirings](https://en.wikipedia.org/wiki/Semiring#Star_semirings):

```{.haskell}
class Semiring a => StarSemiring a where
  star :: a -> a
```

It must satisfy the law:

$a* = 1 + aa* = 1 + a*a$


Defining it for types, for instance:

```{.haskell}
star a = Either () (a, star a)
```

Which is just a standard list!

For monads, the star looks kind of like the [`MonadPlus`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Control-Monad-Fix.html) class, or the [`ArrowLoop`{.haskell}](https://hackage.haskell.org/package/base-4.9.0.0/docs/Control-Arrow.html#t:ArrowLoop) class. I'm not sure if it has an applicative analogy. 

## Weighting

Weighted parsers, regexes, natural lang, constraint programming

## Modules

permutations, replications
http://comonad.com/reader/2011/free-modules-and-functional-linear-functionals/
http://hackage.haskell.org/package/PermuteEffects-0.2/docs/Control-Permute.html
http://hackage.haskell.org/package/ReplicateEffects-0.2/docs/Control-Replicate.html#t:Replicate
