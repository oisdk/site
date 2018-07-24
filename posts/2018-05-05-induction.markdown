---
title: Type-Level Induction in Haskell
tags: Haskell, Dependent Types
---

The code from this post is available as a
[gist](https://gist.github.com/oisdk/23c430b807c788dd43dc4d986c5fdfdd).

One of the most basic tools for use in type-level programming is the Peano definition of the natural numbers:

```haskell
data ℕ
    = Z
    | S ℕ
```

Using the new `TypeFamilyDependencies`{.haskell} extension, these numbers can be used to describe the "size" of some type. I'm going to use the proportion symbol here:

```haskell
type family (t ∷ k) ∝ (n ∷ ℕ) = (a ∷ Type) | a → t n k
```

Then, we can use it to provide an inductive class on the natural numbers:

```haskell
class Finite n where
    induction ∷ t ∝ Z → (∀ k. t ∝ k → t ∝ S k) → t ∝ n

instance Finite Z where
    induction z _ = z
    {-# inline induction #-}

instance Finite n ⇒ Finite (S n) where
    induction z s = s (induction z s)
    {-# inline induction #-}
```

The `induction`{.haskell} function reads as the standard mathematical definition of induction: given a proof (value) of the zero case, and a proof that any proof is true for its successor, we can give you a proof of any finite number.

An added bonus here is that the size of something can usually be resolved at compile-time, so any inductive function on it should also be resolved at compile time.

We can use it to provide the standard instances for basic length-indexed lists:

```haskell
infixr 5 :-
data List n a where
        Nil  ∷ List Z a
        (:-) ∷ a → List n a → List (S n) a
```

Some instances for those lists are easy:

```haskell
instance Functor (List n) where
    fmap _ Nil = Nil
    fmap f (x :- xs) = f x :- fmap f xs
```

However, for `Applicative`{.haskell}, we need some way to recurse on the size of the list. This is where induction comes in.

```haskell
type instance '(List,a) ∝ n = List n a
```

This lets us write `pure`{.haskell} in a pleasingly simple way:

```haskell
instance Finite n ⇒
         Applicative (List n) where
    pure x = induction Nil (x :-)
```

But can we also write `<*>`{.haskell} using induction? Yes! Because we've factored out the induction itself, we just need to describe the notion of a "sized" function:

```haskell
data a ↦ b
type instance ((x ∷ a) ↦ (y ∷ b)) ∝ n = (x ∝ n) → (y ∝ n)
```

Then we can write `<*>`{.haskell} as so:

```haskell
instance Finite n ⇒
         Applicative (List n) where
    pure x = induction Nil (x :-)
    (<*>) =
        induction
            (\Nil Nil → Nil)
            (\k (f :- fs) (x :- xs) → f x :- k fs xs)
```

What about the `Monad`{.haskell} instance? For that, we need a little bit of plumbing: the type signature of `>>=`{.haskell} is:

```haskell
(>>=) ∷ m a → (a → m b) → m b
```

One of the parameters (the second `a`) doesn't have a size: we'll need to work around that, with `Const`{.haskell}:

```haskell
type instance (Const a ∷ ℕ → Type) ∝ n = Const a n
```

Using this, we can write our `Monad`{.haskell} instance:

```haskell
head' ∷ List (S n) a → a
head' (x :- _) = x

tail' ∷ List (S n) a → List n a
tail' (_ :- xs) = xs

instance Finite n ⇒
         Monad (List n) where
    xs >>= (f ∷ a → List n b) =
        induction
            (\Nil _ → Nil)
            (\k (y :- ys) fn → head' (fn (Const y)) :-
                               k ys (tail' . fn . Const . getConst))
            xs
            (f . getConst ∷ Const a n → List n b)
```

## Type Family Dependencies

Getting the above to work actually took a surprising amount of work: the crux is that the `∝`{.haskell} type family needs to be injective, so the "successor" proof can typecheck. Unfortunately, this means that every type can only have one notion of "size". What I'd prefer is to be able to pass in a function indicating exactly *how* to get the size out of a type, that could change depending on the situation. So we could recurse on the first argument of a function, for instance, or just its second, or just the result. This would need either type-level lambdas (which would be cool), or [generalized type family dependencies](https://ghc.haskell.org/trac/ghc/ticket/10832).
