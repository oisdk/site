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

