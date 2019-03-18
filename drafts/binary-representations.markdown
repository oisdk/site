---
title: Binary Representations
tags: Agda, Haskell
bibliography: Agda.bib
---

When we want to work with natural numbers in a language like Agda, we usually
turn to the dreadfully slow Peano implementation:

```agda
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)
```

Often, this is good enough. We usually don't write high-performance systems in
Agda, after all.

If we *do* want to get slightly faster, we can turn to the obvious choice:
binary numbers. As you might imagine, binary numbers for a proof system have
slightly different design requirements than those that form the basis of
Haskell's `Integer` type.

# List-of-Bits

The first representation is the simplest:

```agda
data Bit : Set where O I : Bit

𝔹 : Set
𝔹 = List Bit
```

And it meets the basic requirement: it's faster than Peano numbers. Addition and
multiplication go from $\mathcal{O}(n)$ and $\mathcal{O}(n^2)$ to
$\mathcal{O}(\log_2 n)$ and $\mathcal{O}((\log_2 n) ^ 2)$, respectively.

For use in proofs, though, it has a fatal flaw: trailing zeroes. Because it
doesn't guarantee a unique representation for every natural number, proofs
become much more cumbersome: we would either have to couple the number with a
proof that it's in normal form, or we'd have to prove things about it modulo
trailing zeroes, neither of which is desirable.

# List-of-Gaps

The next representation removes the redundancy by encoding a binary number as a
list of numbers, where each number is the "distance to the next 1".

```agda
Bits : Set
Bits = List ℕ
```

This guarantees a unique representation, at the cost of some complexity. It also
comes with some other nice properties: a non-zero number, for instance, is
always represented by a non-empty list.

While this representation allows for the fast addition and multiplication
described above, it falls down in one area: increments. With Peano numbers,
finding the successor is always a constant-time operation. Binary is slower:

```agda
Bits⁺ : Set
Bits⁺ = ℕ × Bits

inc : Bits → Bits
inc = uncurry _∷_ ∘ inc′
  module Inc where
  mutual
    inc′ : Bits → Bits⁺
    inc′ [] = 0 , []
    inc′ (x ∷ xs) = inc″ x xs

    inc″ : ℕ → Bits → Bits⁺
    inc″ zero ns = map₁ suc (inc′ ns)
    inc″ (suc n) ns = 0 , n ∷ ns
```

On average, we do indeed get $\mathcal{O}(1)$ time: the worst-case can be
$\mathcal{O}(\log_2 n)$, however.

# Skew

A third encoding of binary numbers allows for at most one 2 among all the 1s
and 0s. This strange quirk allows for constant-time increments. To represent it
in Agda, we'll again use a list of gaps, but we'll say that the *second* gap (if
it exists), can represent a 2, if it's 0. This different understanding is
entirely implicit, so we'll need to be careful about encoding the algorithms.

```agda
𝔹 : Set
𝔹 = List ℕ

inc : 𝔹 → 𝔹
inc [] = 0 ∷ []
inc (x ∷ []) = 0 ∷ x ∷ []
inc (x₁ ∷ zero ∷ xs) = suc x₁ ∷ xs
inc (x₁ ∷ suc x₂ ∷ xs) = 0 ∷ x₁ ∷ x₂ ∷ xs
```

As you can see, `inc` is clearly $\mathcal{O}(1)$, and we have a guaranteed
unique representation. Unfortunately, though, we've lost the other efficiencies!
Addition and multiplication have no easy or direct encoding in this system, so
we have to convert back and forth between this and regular binary to perform
them.

# List-of-Segments

The key problem with incrementing in the normal binary system is that it can
cascade: when we hit a long string of 1s, all the 1s become 0 followed by a
single 1. We can turn this problem to our advantage if we use a representation
which encodes both 1s and 0s as strings of gaps. We'll have to use a couple more
tricks to ensure a unique representation, but all in all this is what we have:

```agda
data 0≤_ (A : Set) : Set where
  0₂ : 0≤ A
  0<_ : A → 0≤ A

infixr 5 _0&_ _1&_ B₀_ B₁_ 0<_
mutual
  record 𝔹₀ : Set where
    constructor _0&_
    inductive
    field
      zeroes : ℕ
      tail₁ : 𝔹₁

  record 𝔹₁ : Set where
    constructor _1&_
    inductive
    field
      ones : ℕ
      tail₀ : 0≤  𝔹₀

  data 𝔹⁺ : Set where
    B₀_ : 𝔹₀ → 𝔹⁺
    B₁_ : 𝔹₁ → 𝔹⁺

  𝔹 : Set
  𝔹 = 0≤ 𝔹⁺

inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0₂                               =      B₁ 0     1& 0₂
inc⁺ (0< B₀ zero  0& y 1& xs        ) =      B₁ suc y 1& xs
inc⁺ (0< B₀ suc x 0& y 1& xs        ) =      B₁ 0     1& 0< x 0& y 1& xs
inc⁺ (0< B₁ x 1& 0₂                 ) = B₀ x 0& 0     1& 0₂
inc⁺ (0< B₁ x 1& 0< zero  0& z 1& xs) = B₀ x 0& suc z 1& xs
inc⁺ (0< B₁ x 1& 0< suc y 0& z 1& xs) = B₀ x 0& 0     1& 0< y 0& z 1& xs

inc : 𝔹 → 𝔹
inc x = 0< inc⁺ x
```

# Data Structures

All of these systems are described in Okasaki [-@okasaki_purely_1999, chapter
9.2], where they're used as the basis of data structures. The segmented
representation is the only one which isn't explored in detail: apparently it
works less well as a data structure.
