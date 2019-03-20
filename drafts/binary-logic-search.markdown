---
title: Lazy Numbers and Infinite Search
tags: Agda, Haskell
bibliography: Agda.bib
---

# Number Representations

When working with numbers in Agda, we usually use the following definition:

<style>
.column {
    float: left;
    width: 50%;
}
.row:after {
    content: "";
    display: table;
    clear: both;
}
</style>
<div class="row">
<div class="column">
```haskell
data N = Z | S N deriving (Eq, Ord)

instance Num N where
    Z + n = n
    S n + m = S (n + m)

    Z * m = Z
    S n * m = m + n * m
```
</div>
<div class="column">
```agda
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + y = y
suc x + y = suc (x + y)

_*_ : ℕ → ℕ → ℕ
zero  * y = zero
suc x * y = y + (x * y)
```
</div>
</div>

In Haskell it's less common, for obvious reasons:

| Operation    | Complexity        |
|--------------|-------------------|
| $n + m$      | $\mathcal{O}(n)$  |
| $n \times m$ | $\mathcal{O}(nm)$ |

Why not use built-in integers, then? Two reasons. First, Peano numbers have
magical properties with regards to *laziness*. In both Haskell and Agda, this
means they tend to be more "defined", or, in other words, they can produce some
sensible output without ever looking at their input.

<div class="row">
<div class="column">
```haskell
>>> Z < S undefined
True
```
</div>
<div class="column">
```agda
*-zeroˡ : ∀ x → zero * x ≡ zero
*-zeroˡ x = refl
```
</div>
</div>

In Haskell, as we can see, this lets us run computations without scrutinising
some arguments. Agda benefits similarly: here it lets the compiler see more
"obvious" facts that it may have missed otherwise.

It could be better, though.

<div class="row">
<div class="column">
```haskell
>>> undefined * Z == Z
** Exception: Prelude.undefined
```
</div>
<div class="column">
```agda
*-zeroʳ : ∀ x → x * zero ≡ zero
*-zeroʳ x = refl
-- x * zero != zero of type ℕ
```
</div>
</div>

It tends to be left-biased, examining the first argument in its entirety before
looking at the second.

Is there a way, then, to get the laziness and proof-theoretic benefits of a lazy
number system, but in a more efficient way? Of course!

# List-of-Bits-Binary

The first representation is the simplest:

<div class="row">
<div class="column">
```haskell
data Bit = O | I deriving (Eq, Show, Ord)

type B = [Bit]
```
</div>
<div class="column">
```agda
data Bit : Set where O I : Bit

𝔹 : Set
𝔹 = List Bit
```
</div>
</div>

It might seem strange to implement binary numbers with a singly-linked list, but
it actually does the job pretty well. The time complexities make a dramatic
improvement:

| Operation    | Complexity                    |
|--------------|-------------------------------|
| $n + m$      | $\mathcal{O}(\log_2 n)$       |
| $n \times m$ | $\mathcal{O}(\log_2 (n + m))$ |

For use in proofs, though, it has a fatal flaw: trailing zeroes. This means that
the same number can be represented by multiple lists, making any proofs
significantly more complex. On to our next option:

# List-of-Gaps-Binary

Instead of looking at the bits directly, let's think about a binary number as a
list of chunks of 0s, each followed by a 1. in this way, we simply *can't* have
trailing zeroes, because the definition implies that every number other than 0
ends in 1.

<div class="row">
<div class="column">
```haskell
data Gap = Z | S Gap
type B = [Gap]
```
</div>
<div class="column">
```agda
𝔹 : Set
𝔹 = List ℕ
```
</div>
</div>

This guarantees a unique representation, and has the same improved time
complexity as before. Unfortunately, both of these
representations---list-of-bits and list-of-gaps---have one important operation
that is actually *slower* than on Peano numbers: increment.

<div class="row">
<div class="column">
```haskell
inc :: B -> B
inc = uncurry (flip (:)) . inc'
  where
    inc' [] = ([], Z)
    inc' (x:xs) = inc'' x xs
    
    inc'' Z ns = fmap S (inc' ns)
    inc'' (S n) ns = (n:ns,Z)
```
</div>
<div class="column">
```agda
𝔹⁺ : Set
𝔹⁺ = ℕ × 𝔹

inc : 𝔹 → 𝔹
inc = uncurry _∷_ ∘ inc′
  module Inc where
  mutual
    inc′ : 𝔹 → 𝔹⁺
    inc′ [] = 0 , []
    inc′ (x ∷ xs) = inc″ x xs

    inc″ : ℕ → 𝔹 → 𝔹⁺
    inc″ zero ns = map₁ suc (inc′ ns)
    inc″ (suc n) ns = 0 , n ∷ ns
```
</div>
</div>

On average, we do indeed get $\mathcal{O}(1)$ time: the worst-case can be
$\mathcal{O}(\log_2 n)$, however. There are number of ways to get back that
$\mathcal{O}(1)$ increment, the most famous of which being:

# Skew Binary

This encoding has three digits: 0, 1, and 2. To guarantee a unique
representation, we add the condition that there can be at most one 2 in the
number, which must be the first non-zero digit if it's present.

To represent this we'll encode "gaps", as before, with the condition that if the
second gap is 0 it *actually* represents a 2 digit in the preceding position.
That weirdness out of the way, we are rewarded with an `inc` implementation
which is clearly $\mathcal{O}(1)$.

<div class="row">
<div class="column">
```haskell
inc :: B -> B
inc [] = Z : []
inc (x:[]) = Z : x : []
inc (x  : Z : xs) = S x : xs
inc (x1 : S x2 : xs) = Z : x1 : x2 : xs
```
</div>
<div class="column">
```agda
inc : 𝔹 → 𝔹
inc [] = 0 ∷ []
inc (x ∷ []) = 0 ∷ x ∷ []
inc (x₁ ∷ zero ∷ xs) = suc x₁ ∷ xs
inc (x₁ ∷ suc x₂ ∷ xs) = 0 ∷ x₁ ∷ x₂ ∷ xs
```
</div>
</div>

Unfortunately, though, we've lost the other efficiencies! Addition and
multiplication have no easy or direct encoding in this system, so we have to
convert back and forth between this and regular binary to perform them.

# List-of-Segments

The key problem with incrementing in the normal binary system is that it can
cascade: when we hit a long string of 1s, all the 1s become 0 followed by a
single 1. We can turn this problem to our advantage if we use a representation
which encodes both 1s and 0s as strings of gaps. We'll have to use a couple more
tricks to ensure a unique representation, but all in all this is what we have
(switching to just Agda now):

```agda
data 0≤_ (A : Set) : Set where
  0₂  : 0≤ A
  0<_ : A → 0≤ A

mutual
  record 𝔹₀ : Set where
    constructor _0&_
    inductive
    field
      H₀ : ℕ
      T₀ : 𝔹₁

  record 𝔹₁ : Set where
    constructor _1&_
    inductive
    field
      H₁ : ℕ
      T₁ : 0≤  𝔹₀
open 𝔹₀ public
open 𝔹₁ public

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

The addition implementation is pretty complex, but it does indeed keep the
complexity bounds as required.

# Data Structures

All of these systems are described in Okasaki [-@okasaki_purely_1999, chapter
9.2], where they're used as the basis of data structures. The segmented
representation is the only one which isn't explored in detail: apparently it
works less well as a data structure.

# Logic Programming

Logic programming languages like Prolog allows us to write programs in a truly
declarative way: we say what we want, and the language tries to give it to us.
In a sense, Haskell already has a built-in bare-bones logic language: the list
monad. 

```haskell
pyth :: [(Int,Int,Int)]
pyth = do
  x <- [1..]
  y <- [1..]
  z <- [1..]
  guard (x*x + y*y == z*z)
  return (x,y,z)
```

Unfortunately, it's *really* bare-bones: the example above won't even produce an
output. The problem is that we're performing depth-first search: because the
first list is infinite, we'll never get to the next value for `y`, and never
find a solution.

Even if we fix things by using a different monad instance for `[]`, there are
still areas we can improve, especially with laziness in mind.

Looking again at the triples above:

$$ x^2 + y^2 = z^2 $$

We can notice, for instance, that if $x$ and $y$ are odd, then $z$ must be even.
In other words, we can skip the squaring and addition steps if we first
recognise 

# Lazy Arithmetic, P-Adic Arithmetic Coding, etc
# Curry
# Hilbert
