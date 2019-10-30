---
title: How to do Binary Random-Access Lists Simply
tags: agda
---

"Heterogenous Random-Access lists" by Wouter Swierstra describes how to write a
simple binary random-access list (from Okasaki) to use as a heterogenous tuple.
If you haven't tried to implement the data structure described in the paper
before, you might not realise the just how *elegant* the implementation is.
The truth is that arriving at the definitions presented is difficult: behind
every simple function is a littany of copmlex and ugly alternatives that had to
be tried and discarded first before settling on the final answer.

In this post I want to go through a very similar structure, with special focus
on the "wrong turns" in implementation which can lead to headache.

<!--
```agda
{-# OPTIONS --cubical #-}

open import Prelude
```
-->

# Two Proofs on ℕ, and How to Avoid Them

Here are a couple of important identities on ℕ:

```agda
+0 : ∀ n → n + zero ≡ n
+0 zero    = refl
+0 (suc n) = cong suc (+0 n)

+-suc : ∀ n m → n + suc m ≡ suc n + m
+-suc zero    m = refl
+-suc (suc n) m = cong suc (+-suc n m)
```

These two show up all the time as proof obligations from the compiler (i.e.
"couldn't match type `n + suc m` with `suc n + m`").
The solution is obvious, right?
`subst` in one of the proofs above and you're on your way.
Wait! There might be a better way.

We're going to look at reversing a vector as an example.
We have a normal-looking length-indexed vector:

```agda
infixr 5 _∷_
data Vec (A : Set a) : ℕ → Set a where
  [] : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)
```

Reversing a list is easy: we do it the standard way, in $\mathcal{O}(n)$ time,
with an accumulator:

```agda
data List (A : Set a) : Set a where
  [] : List A
  _∷_ : A → List A → List A

list-reverse : List A → List A
list-reverse = go []
  where
  go : List A → List A → List A
  go acc [] = acc
  go acc (x ∷ xs) = go (x ∷ acc) xs
```

Transferring over to a vector and we see our friends `+-suc` and `+0`.

```agda
vec-reverse₁ : Vec A n → Vec A n
vec-reverse₁ xs = subst (Vec _) (+0 _) (go [] xs)
  where
  go : Vec A n → Vec A m → Vec A (m + n)
  go acc [] = acc
  go acc (x ∷ xs) = subst (Vec _) (+-suc _ _) (go (x ∷ acc) xs)
```

The solution, as with so many things, is to use a fold instead of explicit
recursion.
Folds on vectors are a little more aggresively typed than those on lists:

```agda
foldr : (B : ℕ → Type b)
      → (∀ {n} → A → B n → B (suc n))
      → B zero
      → Vec A n
      → B n
foldr B f b [] = b
foldr B f b (x ∷ xs) = f x (foldr B f b xs)
```

We allow the output type to be indexed by the list of the vector.
This is a good thing, bear in mind: we need that extra information to properly
type `reverse`.

For reverse, unfortunately, we need a *left*-leaning fold, which is a little
trickier to implement than `foldr`.

```agda
foldl : (B : ℕ → Set b)
      → (∀ {n} → B n → A → B (suc n))
      → B zero
      → Vec A n
      → B n
foldl B f b [] = b
foldl B f b (x ∷ xs) = foldl (B ∘ suc) f (f b x) xs
```

With this we can finally `reverse`.

```agda
vec-reverse : Vec A n → Vec A n
vec-reverse = foldl (Vec _) (λ xs x → x ∷ xs) []
```

The real trick in this function is that the type of the return value changes as
we fold.
If you think about it, it's the same optimisation that we make for the
$\mathcal{O}(n)$ reverse on lists: the `B` type above is the "difference list"
in types, allowing us to append on to the end without $\mathcal{O}(n^2)$ proofs.

As an aside, this same trick can let us type the convolve-TABA function quite
simply:

```agda
convolve : Vec A n → Vec B n → Vec (A × B) n
convolve =
  foldl
    (λ n → Vec _ n → Vec _ n)
    (λ { k x (y ∷ ys) → (x , y) ∷ k ys})
    (λ _ → [])
```

# Binary Numbers

Binary numbers come up a lot in dependently-typed programming languages: they
offer an alternative representation of ℕ that's tolerably efifcient (depending
on who's doing the tolerating).
In contrast to the Peano numbers, though, there are a huge number of ways to
implement them.
After trying almost every different way to encode them, I have eventually
settled on the following "best" encoding:

```agda
data Bit : Set where O I : Bit

𝔹⁺ : Set
𝔹⁺ = List Bit

infixr 5 0<_
data 𝔹 : Set where
  0𝕓 : 𝔹
  0<_ : 𝔹⁺ → 𝔹
```
