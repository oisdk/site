---
title: How to do Binary Random-Access Lists Simply
tags: agda
---

"Heterogenous Random-Access Lists" by Wouter Swierstra describes how to write a
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
{-# OPTIONS --cubical --allow-unsolved-metas #-}

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
vec-foldr : (B : ℕ → Type b)
          → (∀ {n} → A → B n → B (suc n))
          → B zero
          → Vec A n
          → B n
vec-foldr B f b [] = b
vec-foldr B f b (x ∷ xs) = f x (vec-foldr B f b xs)
```

We allow the output type to be indexed by the list of the vector.
This is a good thing, bear in mind: we need that extra information to properly
type `reverse`.

For reverse, unfortunately, we need a *left*-leaning fold, which is a little
trickier to implement than `vec-foldr`.

```agda
vec-foldl : (B : ℕ → Set b)
          → (∀ {n} → B n → A → B (suc n))
          → B zero
          → Vec A n
          → B n
vec-foldl B f b [] = b
vec-foldl B f b (x ∷ xs) = vec-foldl (B ∘ suc) f (f b x) xs
```

With this we can finally `reverse`.

```agda
vec-reverse : Vec A n → Vec A n
vec-reverse = vec-foldl (Vec _) (λ xs x → x ∷ xs) []
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
  vec-foldl
    (λ n → Vec _ n → Vec _ n)
    (λ { k x (y ∷ ys) → (x , y) ∷ k ys})
    (λ _ → [])
```

# Binary Numbers

Binary numbers come up a lot in dependently-typed programming languages: they
offer an alternative representation of ℕ that's tolerably efficient (depending
on who's doing the tolerating).
In contrast to the Peano numbers, though, there are a huge number of ways to
implement them.

I'm going to recommend one particular implementation over the others, but before
I do I want to define a function on ℕ:

```agda
2* : ℕ → ℕ
2* zero = zero
2* (suc n) = suc (suc (2* n))
```

In all of the implementations of binary numbers we'll need a function like this.
It is absolutely crucial that it is defined in the way above: the other obvious
definition (`2* n = n + n`) is a nightmare for proofs.

The obvious way (a list of bits) is insufficient, as it allows multiple
representations of the same number (because of the trailing zeroes).
Picking a more clever implementation is tricky, though.
The most obvious one adds a constructor at the top level:

```agda
module OneTerminated where
  infixl 5 _0ᵇ _1ᵇ
  infixr 4 𝕓_

  data 𝔹⁺ : Set where
    1ᵇ : 𝔹⁺
    _0ᵇ _1ᵇ : 𝔹⁺ → 𝔹⁺

  data 𝔹 : Set where
    𝕓0ᵇ : 𝔹
    𝕓_ : 𝔹⁺ → 𝔹
```

𝔹⁺ is the stricly positive natural numbers (i.e. the naturals starting from 1).
𝔹 adds a zero to that set.
This removes the possibility for trailing zeroes, thereby making this
representation unique for every natural number.

<details>
<summary>Evaluation is pretty standard</summary>
```agda
  ⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
  ⟦ 1ᵇ   ⇓⟧⁺ = 1
  ⟦ x 0ᵇ ⇓⟧⁺ =      2* ⟦ x ⇓⟧⁺
  ⟦ x 1ᵇ ⇓⟧⁺ = suc (2* ⟦ x ⇓⟧⁺)

  ⟦_⇓⟧ : 𝔹 → ℕ
  ⟦ 𝕓0ᵇ  ⇓⟧ = 0
  ⟦ 𝕓 x  ⇓⟧ = ⟦ x ⇓⟧⁺
```
</details>

The odd syntax lets us write binary numbers in the natural way:

```agda
  _ : ⟦ 𝕓 1ᵇ 0ᵇ 1ᵇ ⇓⟧ ≡ 5
  _ = refl

  _ : ⟦ 𝕓 1ᵇ 0ᵇ 0ᵇ 1ᵇ ⇓⟧ ≡ 9
  _ = refl
```

I would actually recommend this representation for most use-cases, especially
when you're using binary numbers "as binary numbers", rather than as an abstract
type for faster computation.

Another clever representation is one I wrote about before: the "gapless"
representation.
This is far too much trouble for what it's worth.

Finally, my favourite representation at the moment is *zeroless*.
It has a unique representation for each number, just like the two above, but it
is still a lits of bits.
The difference is that the bits here are 1 and 2, not 0 and 1.

```agda
data Bit : Set where 1ᵇ 2ᵇ : Bit

𝔹 : Set
𝔹 = List Bit
```

Functions like `inc` are not difficult to implement:

```agda
inc : 𝔹 → 𝔹
inc [] = 1ᵇ ∷ []
inc (1ᵇ ∷ xs) = 2ᵇ ∷ xs
inc (2ᵇ ∷ xs) = 1ᵇ ∷ inc xs
```

And evaluation:

```agda
_∷⇓_ : Bit → ℕ → ℕ
1ᵇ ∷⇓ xs =      suc (2* xs)
2ᵇ ∷⇓ xs = suc (suc (2* xs))

⟦_⇓⟧ : 𝔹 → ℕ
⟦_⇓⟧ = foldr _∷⇓_ zero
```

Since we're working in Cubical Agda, we might as well go on and prove that 𝔹 is
isomorphic to ℕ.
I'll include the proof here for completeness, but it's not relevant to the rest
of the post.

<details>
<summary>Proof that 𝔹 and ℕ are isomorphic</summary>
```agda
⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = []
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

2*⇔1ᵇ∷ : ∀ n → inc ⟦ 2* n ⇑⟧ ≡ 1ᵇ ∷ ⟦ n ⇑⟧
2*⇔1ᵇ∷ zero = refl
2*⇔1ᵇ∷ (suc n) = cong (inc ∘ inc) (2*⇔1ᵇ∷ n)

𝔹→ℕ→𝔹 : ∀ n → ⟦ ⟦ n ⇓⟧ ⇑⟧ ≡ n
𝔹→ℕ→𝔹 [] = refl
𝔹→ℕ→𝔹 (1ᵇ ∷ xs) = 2*⇔1ᵇ∷ ⟦ xs ⇓⟧ ; cong (1ᵇ ∷_) (𝔹→ℕ→𝔹 xs)
𝔹→ℕ→𝔹 (2ᵇ ∷ xs) = cong inc (2*⇔1ᵇ∷ ⟦ xs ⇓⟧) ; cong (2ᵇ ∷_) (𝔹→ℕ→𝔹 xs)

inc⇔suc : ∀ n → ⟦ inc n ⇓⟧ ≡ suc ⟦ n ⇓⟧
inc⇔suc [] = refl
inc⇔suc (1ᵇ ∷ xs) = refl
inc⇔suc (2ᵇ ∷ xs) = cong (suc ∘ 2*) (inc⇔suc xs)

ℕ→𝔹→ℕ : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
ℕ→𝔹→ℕ zero = refl
ℕ→𝔹→ℕ (suc n) = inc⇔suc ⟦ n ⇑⟧ ; cong suc (ℕ→𝔹→ℕ n)

𝔹⇔ℕ : 𝔹 ⇔ ℕ
𝔹⇔ℕ = iso ⟦_⇓⟧ ⟦_⇑⟧ ℕ→𝔹→ℕ 𝔹→ℕ→𝔹
```
</details>

# Arrays

Now on to the binary random-access list.

```agda
infixr 5 _1∷_ _2∷_
data Array (T : ℕ → Type a) : 𝔹 → Type a where
  [] : Array T []
  _1∷_ : ∀ {ns} → T 0 → Array (T ∘ suc) ns → Array T (1ᵇ ∷ ns)
  _2∷_ : ∀ {ns} → T 1 → Array (T ∘ suc) ns → Array T (2ᵇ ∷ ns)
```

```agda
cons : ∀ {a} {A : ℕ → Type a}
     → (_∙_ : ∀ {n} → A n → A n → A (suc n))
     → ∀ {ns}
     → A 0 → Array A ns → Array A (inc ns)
cons _∙_ x [] = x 1∷ []
cons _∙_ x (y 1∷ ys) = (x ∙ y) 2∷ ys
cons _∙_ x (y 2∷ ys) = x 1∷ cons _∙_ y ys
```

```agda
2^_*_ : ℕ → ℕ → ℕ
2^ zero  * n = n
2^ suc m * n = 2* (2^ m * n)
```

```agda
foldrArray : {A : ℕ → Type a}
           → (B : ℕ → Type b)
           → (∀ n {m} → A n → B (2^ n * m) → B (2^ n * suc m))
           → B zero → ∀ {ns} → Array A ns → B ⟦ ns ⇓⟧
foldrArray B c b []        = b
foldrArray B c b (x 1∷ xs) = c 0 x (foldrArray (B ∘ 2*) (c ∘ suc) b xs)
foldrArray B c b (x 2∷ xs) = c 1 x (foldrArray (B ∘ 2*) (c ∘ suc) b xs)
```

```agda
data Fin𝔹 (A : Set a) : 𝔹 → Type a where
  here₁ : ∀ {ns}                         → Fin𝔹 A (1ᵇ ∷ ns)
  here₂ : ∀ {ns}   → (i : A)             → Fin𝔹 A (2ᵇ ∷ ns)
  there : ∀ {n ns} → (i : A) → Fin𝔹 A ns → Fin𝔹 A (n  ∷ ns)
```

```agda
lookup : ∀ {a i} {I : Type i} {A : ℕ → Type a}
       → (ind : ∀ {n} → I → A (suc n) → A n)
       → ∀ {ns}
       → Array A ns
       → Fin𝔹 I ns
       → A 0
lookup ind (x 1∷ xs) here₁ = x
lookup ind (x 1∷ xs) (there i is) = ind i (lookup ind xs is)
lookup ind (x 2∷ xs) (here₂ i)    = ind i x
lookup ind (x 2∷ xs) (there i is) = ind i (lookup ind xs is)
```

```agda
Perfect : Set a → ℕ → Set a
Perfect A zero = A
Perfect A (suc n) = Perfect (A × A) n

branch : ∀ n → Perfect A n → Perfect A n → Perfect A (suc n)
branch zero = _,_
branch (suc n) = branch n

foldrPerf : (B : ℕ → Type b)
          → (∀ {n} → A → B n → B (suc n))
          → ∀ n {m}
          → Perfect A n
          → B (2^ n * m)
          → B (2^ n * suc m)
foldrPerf B f zero = f
foldrPerf B f (suc n) =
  foldrPerf (B ∘ 2*) (λ { (x , y) zs → f x (f y zs) }) n

toVec : ∀ {ns} → Array (Perfect A) ns → Vec A ⟦ ns ⇓⟧
toVec = foldrArray (Vec _) (foldrPerf (Vec _) _∷_) []

fromVec : ∀ {n} → Vec A n → Array (Perfect A) ⟦ n ⇑⟧
fromVec = vec-foldr (Array (Perfect _) ∘ ⟦_⇑⟧) (cons (λ {n} → branch n)) []
```
