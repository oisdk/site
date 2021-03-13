---
title: Hyperfunctions
tags: Haskell
bibliography: Hyperfunctions.bib
---

Check out this type:

```haskell
newtype a -&> b = Hyp { invoke :: (b -&> a) -> b } 
```

I came across this type a few months ago, and for my money it's the most
interesting newtype you can write in Haskell.
The theory behind it is pretty mind-bending and fascinating, but even more
surprisingly it has some practical uses in optimisation.
Let's find out about it!

Values of the type `a -&> b` are called *hyperfunctions*
[@launchbury_coroutining_2013; -@launchbury_zip_2000; -@krstic_category_2000].
If we expand it out a bit we can see that it's an infinitely left-nested
function, which takes in some `a`s and returns some `b`s---kind of.


```haskell
type a -&> b = (b -&> a) -> b
             = ((a -&> b) -> a) -> b
             = (((b -&> a) -> b) -> a) -> b
             = ((((... -> b) -> a) -> b) -> a) -> b
```

By "takes in some `a`s" I mean it takes in a function which *returns* an `a`.
That function, in turn, takes in something which returns a `b`, which takes in
something which returns an `a`, and so on.
So all of the `a`s end up in negative positions, and all of the `b`s in
positive.
This actually leads to the first interesting thing about this type:


# Hyperfunctions Don't Exist in Set Theory

Haskell types aren't the same as sets.
That's not just because they're recursive; types like the following form
completely reasonable sets:

```haskell
data Nat = Z | S Nat
```

It's actually because of the presence of types like `a -&> b`: such types run
into "size problems" (read: they allow for paradoxes, or proofs of false).

Interestingly, the type *also* doesn't exist in some type theories!
In Agda, for instance, we're not allowed to define it:

```agda
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inductive; constructor hyp
  field invoke : (B ↬ A) → B
```

And for good reason!
If we turn off the positivity checker, we can write Curry's paradox (example
proof taken from [here](https://stackoverflow.com/a/51253757/4892417)):

```agda
yes? : ⊥ ↬ ⊥
yes? .invoke h = h .invoke h

no! : (⊥ ↬ ⊥) → ⊥
no! h = h .invoke h

boom : ⊥
boom = no! yes?
```

Note that this isn't an issue with the termination checker: 
