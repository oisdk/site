---
title: Lazy Binary Numbers
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
<div class="row">
<div class="column">
Haskell
</div>
<div class="column">
Agda
</div>
</div>

In Haskell it's less common, for obvious reasons:

| Operation    | Complexity        |
|--------------|-------------------|
| $n + m$      | $\mathcal{O}(n)$  |
| $n \times m$ | $\mathcal{O}(nm)$ |

Why use them at all, then? Well, in Agda, we need them so we can *prove* things
about the natural numbers. Machine-level integers are fast, but they're opaque:
their implementation isn't written in Agda, and therefore it's not available for
the compiler to reason about.

In Haskell, they occasionally find uses due to their
*laziness*. This can help in Agda as well. By lazy here I mean that operations
on them don't have to inspect the full structure before giving some output.

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

It's not *completely* lazy, though. In particular, it tends to be left-biased:

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

Like Boolean short-circuiting operators, operations on Peano numbers will
usually have to scrutinise the left-hand-side argument quite a bit before giving
an output.

So, Peano numbers are good because:

#. We can prove things about them.
#. They're lazy.

In this post, I'm going to look at some other number representations that
maintain these two desirable properties, while improving on the efficiency
somewhat. 

## List-of-Bits-Binary

The first option for an improved representation is binary numbers. We can
represent binary numbers as a list of bits:

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

As we're using these to represent natural numbers, we'll need to define a way to
convert between them:

<div class="row">
<div class="column">
```haskell
eval :: B -> N
eval = foldr f Z
  where
    f O xs = xs + xs
    f I xs = S (xs + xs)

inc :: B -> B
inc [] = [I]
inc (O:xs) = I : xs
inc (I:xs) = O : inc xs

fromN :: N -> B
fromN Z = []
fromN (S n) = inc (fromN n)
```
</div>
<div class="column">
```agda
⟦_⇓⟧ : 𝔹 → ℕ
⟦_⇓⟧ = foldr (λ { O xs → xs + xs
                ; I xs → suc (xs + xs) })
             zero

inc : 𝔹 → 𝔹
inc [] = I ∷ []
inc (O ∷ xs) = I ∷ xs
inc (I ∷ xs) = O ∷ inc xs

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = []
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧
```
</div>
</div>

And here we run into our first problem: redundancy. There are multiple ways to
represent the same number according to the semantics defined above. We can
actually prove this in Agda:

```agda
redundant : ∃₂ λ x y → x ≢ y × ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧
redundant = [] , O ∷ [] , (λ ()) , refl
```

In English: "There are two binary numbers which are not the same, but which do
evaluate to the same natural number". 
(This proof was actually automatically filled in for me after writing the
signature)

This represents a huge problem for proofs. It means that even simple things like
$x \times 0 = 0$ aren't true, depending on how multiplication is implemented. On
to our next option:

## List-of-Gaps-Binary

Instead of looking at the bits directly, let's think about a binary number as a
list of chunks of 0s, each followed by a 1. 
In this way, we simply *can't* have trailing zeroes, because the definition
implies that every number other than 0 ends in 1.

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

This guarantees a unique representation.
As in the representation above, it has much improved time complexities for the
familiar operations:

| Operation    | Complexity                    |
|--------------|-------------------------------|
| $n + m$      | $\mathcal{O}(\log_2 n)$       |
| $n \times m$ | $\mathcal{O}(\log_2 (n + m))$ |

Encoding the zeroes as gaps also makes multiplication much faster in certain
cases: multiplying by a high power of 2 is a constant-time operation, for
instance.

It does have one disadvantage, and it's to do with the increment function:

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

With all of their problems, Peano numbers performed this operation in constant
time. The above implementation is only *amortised* constant-time, though, with a
worst case of $\mathcal{O}(\log_2 n)$ 
(same as the list-of-bits version).
There are a number of ways to remedy this, the most famous being:

## Skew Binary

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

## List-of-Segments-Binary

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

Perfect! Increments are obviously $\mathcal{O}(1)$, and we've guaranteed a
unique representation.

I've been working on this type for a couple of days, and you can see my code
[here](https://github.com/oisdk/agda-binary/).
So far, I've done the following:

Defined `inc`, addition, and multiplication

:   These were a little tricky to get right ([addition is particularly
    hairy](https://github.com/oisdk/agda-binary/blob/master/Data/Binary/Operations/Addition.agda#L9)),
    but they're all there, and maximally lazy.
   
Proved Homomorphism

:   For each one of the functions, you want them to correspond precisely to the
    equivalent functions on Peano numbers. Proving that fact amounts to filling
    in definitions for the following:
    
    ```agda
    inc-homo : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
    +-homo : ∀ x y → ⟦ x + y ⇓⟧ ≡ ⟦ x ⇓⟧ + ⟦ y ⇓⟧
    *-homo : ∀ x y → ⟦ x * y ⇓⟧ ≡ ⟦ x ⇓⟧ * ⟦ y ⇓⟧
    ```
     
Proved Bijection

:   As we went to so much trouble, it's important to prove that these numbers
    form a one-to-one correspondence with the Peano numbers. As well as that,
    once done, we can use it to prove facts about the homomorphic functions
    above, by reusing any proofs about the same functions on Peano numbers. For
    instance, here is a proof of commutativity of addition:

    ```agda
    +-comm : ∀ x y → x + y ≡ y + x
    +-comm x y = injective (+-homo x y ⟨ trans ⟩
                            ℕ.+-comm ⟦ x ⇓⟧ ⟦ y ⇓⟧ ⟨ trans ⟩
                            sym (+-homo y x))
    ```

# Applications

So now that we have our nice number representation, what can we do with it?
One use is as a general-purpose number type in Agda: it represents a good
balance between speed and "proofiness", and Coq uses a similar type in its
standard library.

There are other, more unusual uses of such a type, though.

## Data Structures

It's a well-known technique to build a data structure out of some number
representation [@hinze_numerical_1998]: in fact, all of the representations
above are explored in Okasaki [-@okasaki_purely_1999, chapter 9.2].

## Logic Programming

Logic programming languages like Prolog let us write programs in a backwards
kind of way. We say what the output looks like, and the unifier will figure out
the set of inputs that generates it.

In Haskell, we have a very rough approximation of a similar system: the list
monad.

```haskell
pyth :: [(Int,Int,Int)]
pyth = do
  x <- [1..10]
  y <- [1..10]
  z <- [1..10]
  guard (x*x + y*y == z*z)
  return (x,y,z)
```

There are tons of inefficiencies in the above code: for us, though, we can look
at one: the number representation. In the equation:

$$x^2 + y^2 = z^2$$

If we know that $x$ and $y$ are both odd, then $z$ must be even. If the
calculation of the equation is expensive, this is precisely the kind of shortcut
we'd want to take advantage of. Luckily, our binary numbers do just that: it is
enough to scrutinise just the first bits of $x$ and $y$ in order to determine
the first bit of the output.

After seeing that example, you may be thinking that lazy evaluation is a perfect
fit for logic programming.
You're not alone! Curry [@Hanus16Curry] is a lazy, functional logic programming
language, with a similar syntax to Haskell. It also uses lazy binary numbers to
optimise testing.

## Lazy Predicates

In order for queries to be performed efficiently on binary numbers, we will also
need a way to describe lazy *predicates* on them. A lot of these predicates are
more easily expressible on the list-of-bits representation above, so we'll be
working with that representation for this bit. Not to worry, though: we can
convert from the segmented representation into the list-of-bits, and [we can
prove that the conversion is
injective](https://github.com/oisdk/agda-binary/blob/fb89ba5ae3b2aa0cb95301da42c8dbf27048181b/Data/Binary/Bits.agda#L52):

```agda
toBits-injective : ∀ xs ys → toBits xs ≡ toBits ys → xs ≡ ys
```

Here's the curious problem: since our binary numbers are expressed
least-significant-bit-first, we have to go to the end before knowing which is
bigger. Luckily, we can use one of my favourite Haskell tricks, involving the
ordering monoid:

```agda
data Ordering : Set where
  lt eq gt : Ordering

_∙_ : Ordering → Ordering → Ordering
lt ∙ y = lt
eq ∙ y = y
gt ∙ y = gt

cmpBit : Bit → Bit → Ordering
cmpBit O O = eq
cmpBit O I = lt
cmpBit I O = gt
cmpBit I I = eq

compare : Bits → Bits → Ordering
compare [] [] = eq
compare [] (_ ∷ _) = lt
compare (_ ∷ _) [] = gt
compare (x ∷ xs) (y ∷ ys) = compare xs ys ∙ cmpBit x y
```

Thanks to laziness, this function first compares the length of the lists, and
then does a lexicographical comparison in reverse only if the lengths are the
same. This is exactly what we want for our numbers.

# Future Posts

That's all I have for now, but I'm interested to formalise the laziness of these
numbers in Agda. Usually that's done with coinduction: I would also like to see
the relationship with exact real arithmetic.

I wonder if it can be combined with @oconnor_applications_2016 to get some
efficient proof search algorithms, or with @escardo_seemingly_2014 to get more
efficient exhaustive search.

# References
