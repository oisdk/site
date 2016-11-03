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
```
```{.haskell .literate .prop}
add xs == sum xs
```
