---
title: Revisiting a Trie in Haskell
tags: Haskell
description: Generalizing a Trie using Monoids
---

This post is a part-2 from [this](2015-10-06-haskell-trie-lhs.html) post.

# Conforming to Foldable

When I ended the last post, I had a nice `Trie`{.haskell} datatype, with plenty of functions, but I couldn't get it to conform to the standard Haskell classes. The problem was to do with the type variables in the Trie:

```{.haskell .literate .hidden_source}
{-# language GADTs, FlexibleInstances, TypeFamilies #-}
{-# language DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
{-# language FunctionalDependencies, FlexibleInstances #-}

module Tries where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Foldable hiding (toList)
import Prelude hiding (lookup)
import Data.Monoid
import GHC.Exts (IsList(..))
```
```{.haskell .literate}
data OldTrie a = OldTrie
  { otEndHere  :: Bool
  , otChildren :: Map a (OldTrie a) }
```

Although the type variable is `a`{.haskell}, the trie really contains *lists* of `a`{.haskell}s. At least, that's what's reflected in functions like `insert`{.haskell}, `member`{.haskell}, etc.:

```{.haskell .literate}
member :: (Foldable f, Ord a) => f a -> OldTrie a -> Bool
member = foldr f otEndHere where
  f e a = maybe False a . Map.lookup e . otChildren
  
otInsert :: (Foldable f, Ord a) => f a -> OldTrie a -> OldTrie a
otInsert = foldr f b where
  b (OldTrie _ c) = OldTrie True c
  f e a (OldTrie n c) = OldTrie n (Map.alter (Just . a . fold) e c)
  
instance Ord a => Monoid (OldTrie a) where
  mempty = OldTrie False mempty
  OldTrie v c `mappend` OldTrie t d = 
    OldTrie (v || t) (Map.unionWith (<>) c d)
```

Realistically, the type which the trie contains is more like:

```haskell
Foldable f => Trie (f a)
```

That signature strongly hints at GADTs, as was indicated by [this stackoverflow answer](http://stackoverflow.com/questions/33469157/foldable-instance-for-a-trie-set). The particular GADT which is applicable here is this:

```{.haskell .literate}
data TrieSet a where TrieSet :: Bool -> Map a (TrieSet [a]) -> TrieSet [a]
```

```{.haskell .literate .hidden_source}
tsEndHere :: TrieSet [a] -> Bool
tsEndHere (TrieSet e _) = e

tsChildren :: TrieSet [a] -> Map a (TrieSet [a])
tsChildren (TrieSet _ c) = c

tsInsert :: (Foldable f, Ord a) => f a -> TrieSet [a] -> TrieSet [a]
tsInsert = foldr f b where
  b :: TrieSet [a] -> TrieSet [a]
  f :: Ord a => a -> (TrieSet [a] -> TrieSet [a]) -> TrieSet [a] -> TrieSet [a]

  b (TrieSet _ c) = TrieSet True c
  f e a (TrieSet n c) = TrieSet n (Map.alter (Just . a . fold) e c)
  
instance Ord a => Monoid (TrieSet [a]) where
  mempty = TrieSet False Map.empty
  TrieSet v c `mappend` TrieSet t d = 
    TrieSet (v || t) (Map.unionWith (<>) c d)
```

Why lists and not a general `Foldable`{.haskell}? Well, for the particular use I had in mind (conforming to the `Foldable`{.haskell} typeclass), I need `(:)`{.haskell}.

```{.haskell .literate}
instance Foldable TrieSet where
  foldr f b (TrieSet e c) = if e then f [] r else r where
    r = Map.foldrWithKey (flip . g . (:)) b c
    g k = foldr (f . k)
```

With some more helper functions, the interface becomes pretty nice:

```{.haskell .literate}
instance Show a => Show (TrieSet [a]) where
  showsPrec d t = 
    showParen 
      (d > 10)
      (showString "fromList " . shows (foldr (:) [] t))

instance Ord a => IsList (TrieSet [a]) where
  type Item (TrieSet [a]) = [a]
  fromList = foldr tsInsert mempty
  toList = foldr (:) []
```

The trie has the side-effect of lexicographically sorting what it's given:

```{.haskell .literate .example .hidden_source}
:set -XGADTs

```
```{.haskell .literate .example}
fromList ["ced", "abc", "ced", "cb", "ab"] :: TrieSet String
fromList ["ab","abc","cb","ced"]
```

# Further Generalizing

Most implementations of tries that I've seen are map-like data structures, rather than set-like. In other words, instead of holding a `Bool`{.haskell} at the value position, it holds a `Maybe`{.haskell} something. 

```{.haskell .literate}

data Trie a b = Trie
  { endHere  :: b
  , children :: Map a (Trie a b) 
  } deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
```

This is a much more straightforward datatype. `Foldable`{.haskell} can even be automatically derived. 

However, I haven't made the `endHere`{.haskell} field a `Maybe a`{.haskell}. I want to be able to write something like this:

```haskell
type TrieSet [a] = Trie a Bool
type TrieMap a b = Trie a (Maybe b)
```

And have it automatically choose the implementation of the functions I need[^1].

To do that, though, I'll need to write the base functions, agnostic of the type of `b`. I *can* rely on something like `Monoid`{.haskell}, though:

```{.haskell .literate}
instance (Ord a, Monoid b) => Monoid (Trie a b) where
  mempty = Trie mempty Map.empty
  mappend (Trie v k) (Trie t l) = 
    Trie (v <> t) (Map.unionWith (<>) k l)
```

In fact, quite a lot of functions naturally lend themselves to this fold + monoid style:

```{.haskell .literate}
lookup :: (Ord a, Monoid b, Foldable f) 
       => f a -> Trie a b -> b
lookup = foldr f endHere where
  f e a = foldMap a . Map.lookup e . children

insert' :: (Foldable f, Ord a, Monoid b) 
       => f a -> b -> Trie a b -> Trie a b
insert' xs v = foldr f b xs where
  b (Trie p c) = Trie (v <> p) c
  f e a (Trie n c) = 
    Trie n (Map.alter (Just . a . fold) e c) 
```

A monoid is needed for the values, though, and neither `Bool`{.haskell} nor `∀ a. Maybe a`{.haskell} conform to `Monoid`{.haskell}. Looking back to the implementation of the trie-set, the `(||)`{.haskell} function has been replaced by `mappend`{.haskell}. There *is* a newtype wrapper in `Data.Monoid`{.haskell} which has exactly this behaviour, though: `Any`{.haskell}.

Using that, the type signatures specialize to:

```haskell
type TrieSet a = Trie a Any
lookup :: (Ord a, Foldable f) 
       => f a -> TrieSet a -> Any
insert :: (Ord a, Foldable f) 
       => f a -> Any -> TrieSet a -> TrieSet a
```

Similarly, for `Maybe`{.haskell}, there's both `First`{.haskell} and `Last`{.haskell}. They have the behaviour:

```{.haskell .literate .prop}
First (Just x) <> First (Just y) == First (Just x)
```
```{.haskell .literate .prop}
Last  (Just x) <> Last  (Just y) == Last  (Just y)
```

I think it makes more sense for a value inserted into a map to overwrite whatever was there before. Since the newer value is on the left in the `mappend`{.haskell}, then, `First`{.haskell} makes most sense.

```haskell
type TrieMap a b = Trie a (First b)
lookup :: (Ord a, Foldable f) => f a -> TrieMap a b -> First b
insert :: (Ord a, Foldable f) 
       => f a -> First b -> TrieMap a b -> TrieMap a b
```

There are some other ways that you can interpret the monoid. For instance, subbing in `Sum Int`{.haskell} gives you a bag-like trie:

```haskell
type TrieBag a = Trie a (Sum Int)
lookup :: (Ord a, Foldable f) => f a -> TrieBag a -> Sum Int
insert :: (Ord a, Foldable f) 
       => f a -> Sum Int -> TrieBag a -> TrieBag a
```

This is a set which can store multiple copies of each member. Turned the other way around, a map which stores many values for each key looks like this:

```haskell
type TrieBin a b = Trie a [b]
lookup :: (Ord a, Foldable f) => f a -> TrieBin a b -> [b]
insert :: (Ord a, Foldable f) 
       => f a -> [b] -> TrieBin a b -> TrieBin a b
```

This method so far isn't really satisfying, though. Really, the `insert`{.haskell} signatures should look like this:

```haskell
insert :: (Ord a, Foldable f) 
       => f a -> b -> TrieMap a b -> TrieMap a b
insert :: (Ord a, Foldable f)
       => f a -> b -> TrieBin a b -> TrieBin a b
```

Modifying insert slightly, you can get exactly that:

```{.haskell .literate}
insert :: (Foldable f, Ord a, Applicative c, Monoid (c b)) 
       => f a -> b -> Trie a (c b) -> Trie a (c b)
insert xs v = foldr f b xs where
  b (Trie p c) = Trie (pure v <> p) c
  f e a (Trie n c) = Trie n (Map.alter (Just . a . fold) e c)
```

`pure`{.haskell} from `Applicative`{.haskell} is needed for the "embedding".


Similarly, the "inserting" for the set-like types isn't really right. The value argument is out of place. This should be the signature:

```haskell
add :: (Ord a, Foldable f) 
    => f a -> TrieSet a -> TrieSet a
add :: (Ord a, Foldable f)
    => f a -> TrieBin a -> TrieBin a
```

In particular, while we have an "empty" thing (0, False) for monoids, we need a "one" thing (1, True) for this function. A semiring[^2] gives this exact method:

```{.haskell .literate}
class Monoid a => Semiring a where
  one :: a
  mul :: a -> a -> a
  
instance Num a => Semiring (Sum a) where
  one = 1
  mul = (*)

instance Semiring Any where
  one = Any True
  Any x `mul` Any y = Any (x && y)
```

This class is kind of like a combination of both monoid wrappers for both `Int`{.haskell} and `Bool`{.haskell}. You could take advantage of that:

```{.haskell .literate}

class (Monoid add, Monoid mult)
  => SemiringIso a add mult | a -> add, a -> mult where
    toAdd    :: a -> add
    fromAdd  :: add -> a
    toMult   :: a -> mult
    fromMult :: mult -> a
  
(<+>), (<.>) :: SemiringIso a add mult => a -> a -> a

x <+> y = fromAdd  (toAdd  x <> toAdd  y)
x <.> y = fromMult (toMult x <> toMult y)

instance SemiringIso Int (Sum Int) (Product Int) where
  toAdd    = Sum
  fromAdd  = getSum
  toMult   = Product
  fromMult = getProduct
  
instance SemiringIso Bool Any All where
  toAdd    = Any
  fromAdd  = getAny
  toMult   = All
  fromMult = getAll
```

But it seems like overkill.

Anyway, assuming that we have the functions from `Semiring`{.haskell}, here's the `add` function:

```{.haskell .literate}
add :: (Foldable f, Ord a, Semiring b) 
    => f a -> Trie a b -> Trie a b
add xs = foldr f b xs where
  b (Trie p c) = Trie (one <> p) c
  f e a (Trie n c) = 
    Trie n (Map.alter (Just . a . fold) e c)
```

Now, expressions can be built up without specifying the specific monoid implementation, and the whole behaviour can be changed with a type signature:

```{.haskell .literate .hidden_source}
instance (Ord a, Semiring b) => IsList (Trie a b) where
  type Item (Trie a b) = [a]
  fromList = foldr add mempty
ans :: Semiring b => b
```
```{.haskell .literate}
ans = lookup "abc" (fromList ["abc", "def", "abc", "ghi"])
```
```{.haskell .literate .example}
ans :: Sum Int
Sum {getSum = 2}
```
```{.haskell .literate .example}
ans :: Any
Any {getAny = True}
```

Slightly fuller implementations of all of these are available [here](https://github.com/oisdk/hstrie).

[^1]: Kind of like [program inference in lieu of type inference](https://www.youtube.com/watch?v=3U3lV5VPmOU)
[^2]: This isn't really a very good definition of semiring. While Haskell doesn't have this class in base, [Purescript has it in their prelude.](https://github.com/purescript/purescript-prelude/blob/master/src/Data/Semiring.purs)
