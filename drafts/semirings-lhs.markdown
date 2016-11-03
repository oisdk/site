---
title: Semirings
tags: Haskell
---
```{.haskell .literate .hidden_source}
module Semirings where
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

I got using semirings first to try and avoid code duplication for a trie implementation. Basically, I wanted to be able to write one map-like type, and decide whether it was a set, map, multimap, multiset, etc. based on types. (and avoiding `newtype`{.haskell}s as much as possible) `Monoid`{.haskell}s worked for a while:

```{.haskell .literate}
newtype GeneralMap a b = GeneralMap
  { getMap :: Map.Map a b
  } deriving (Functor, Show, Eq, Ord)

lookup :: (Ord a, Monoid b) => a -> GeneralMap a b -> b
lookup x = fold . Map.lookup x . getMap

insert :: (Ord a, Applicative f, Monoid (f b)) => a -> b -> GeneralMap a (f b) -> GeneralMap a (f b)
insert k v = GeneralMap . Map.insertWith mappend k (pure v) . getMap

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
insert :: Ord a => a -> b -> Map a b -> Map a b
delete :: Ord a => a -> Map a b -> Map a b

lookup :: Ord a => a -> MultiMap a b -> [b]
insert :: Ord a => a -> b -> MultiMap a b -> MultiMap a b
delete :: Ord a => a -> MultiMap a b -> MultiMap a b
```

Sets need `one`{.haskell}, though:

```{.haskell .literate}
add :: (Ord a, Semiring b) => a -> GeneralMap a b -> GeneralMap a b
add x = GeneralMap . Map.insertWith (<+>) x one . getMap
```

```{.haskell}
```
