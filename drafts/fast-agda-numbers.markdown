---
title: Writing a Fast Number Implementation in Agda
tags: Agda
---

I've been messing around with some binary number implementations in Agda
recently and I have come across a few tricks to make the representation work
quickly.
In this post I'll go through a few of those tricks, which might be helpful for
other people writing Agda and struggling through its slowness.

# The Representation

First things first, I'm using zeroless binary numbers as the basic
representation.
They look like the following:

```agda
infixr 8 1ᵇ_ 2ᵇ_
data 𝔹 : Type₀ where
  0ᵇ : 𝔹
  1ᵇ_ 2ᵇ_ : 𝔹 → 𝔹
```

As you can see, this type is basically a list of booleans: it might be tempting,
therefore, to redefine the type in terms of lists and bools:

```agda
𝔹 : Type₀
𝔹 = List Bool

infixr 8 1ᵇ_ 2ᵇ_
pattern 0ᵇ = []
pattern 1ᵇ_ xs = false ∷ xs
pattern 2ᵇ_ xs = true  ∷ xs
```

Unfortunately, though, that will incur a pretty serious performance hit.
Agda tends to slow down when used with complex, nested types: the simple
non-parameterised type we defined first tends to work much faster.

# Conversion

The next thing to consider is the function to convert to and from the natural
numbers.
The conversion to is as follows:

```agda
⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0ᵇ ⇓⟧ = 0
⟦ 1ᵇ xs ⇓⟧ = 1 + ⟦ xs ⇓⟧ * 2
⟦ 2ᵇ xs ⇓⟧ = 2 + ⟦ xs ⇓⟧ * 2
```

By using `+` and `*` here, we can leverage Agda's faster built-in natural number
types.
Those functions will call out to actually fast (ish) implementations on
Haskell's `Integer` type.
The actual expressions we use are quite important for proofs: we want to write
`n * 2` instead of `2 * n`, for instance, wherever possible.
This allows the proof that the binary numbers are isomorphic to the Peano to be
quite short:

<details>
<summary>Proof of isomorphism</summary>

```agda
inc-suc : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-suc 0ᵇ     i = 1
inc-suc (1ᵇ x) i = 2 ℕ.+ ⟦ x ⇓⟧ ℕ.* 2
inc-suc (2ᵇ x) i = suc (inc-suc x i ℕ.* 2)

inc-2*-1ᵇ : ∀ n → inc ⟦ n ℕ.* 2 ⇑⟧ ≡ 1ᵇ ⟦ n ⇑⟧
inc-2*-1ᵇ zero    i = 1ᵇ 0ᵇ
inc-2*-1ᵇ (suc n) i = inc (inc (inc-2*-1ᵇ n i))

𝔹-rightInv : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
𝔹-rightInv zero    = refl
𝔹-rightInv (suc x) = inc-suc ⟦ x ⇑⟧ ; cong suc (𝔹-rightInv x)

𝔹-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
𝔹-leftInv 0ᵇ = refl
𝔹-leftInv (1ᵇ x) =           inc-2*-1ᵇ ⟦ x ⇓⟧  ; cong 1ᵇ_ (𝔹-leftInv x)
𝔹-leftInv (2ᵇ x) = cong inc (inc-2*-1ᵇ ⟦ x ⇓⟧) ; cong 2ᵇ_ (𝔹-leftInv x)

𝔹⇔ℕ : 𝔹 ⇔ ℕ
𝔹⇔ℕ .fun = ⟦_⇓⟧
𝔹⇔ℕ .inv = ⟦_⇑⟧
𝔹⇔ℕ .rightInv = 𝔹-rightInv
𝔹⇔ℕ .leftInv  = 𝔹-leftInv
```
</details>

The other function, converting *from* a peano number, is where performance
becomes a little trickier to achieve:

```agda
⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧
```

# Strictness

The above conversion from the natural numbers is a classic example of a
space-leak in a language like Haskell.
Perhaps a little surprisingly, laziness itself isn't the culprit: the space leak
above would occur in a strict language also.
The problem is that we will build up a long chain of calls to `inc` before
evaluating any of them.
Where laziness does become a problem is when we attempt to solve the problem in
the traditional way: with an accumulator.

```agda
⟦_⇑⟧ : ℕ → 𝔹
⟦_⇑⟧ = go 0ᵇ
  where
  go : 𝔹 → ℕ → 𝔹
  go a zero    = a
  go a (suc n) = go (inc a) n
```

Here, laziness will preserve the space leak, since we don't force the evaluation
of `a` at any point.

Agda does have some strictness primitives, however, which we can use with the
following helper functions:

```agda
infixr 0 _$!_
_$!_ : {A : Type a} {B : A → Type b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f
{-# INLINE _$!_ #-}

infixr 0 let-bang
let-bang : {A : Type a} {B : A → Type b} → ∀ x → (∀ x → B x) → B x
let-bang = primForce
{-# INLINE let-bang #-}

syntax let-bang v (λ x → e) = let! x =! v in! e
```

This transforms our conversion function into the following:

```agda
⟦_⇑⟧ : ℕ → 𝔹
⟦_⇑⟧ = go 0ᵇ
  where
  go : 𝔹 → ℕ → 𝔹
  go a zero    = a
  go a (suc n) = let! a′ =! inc a in! go a′ n
```

(you do have to write a strict version of `inc` as well)

Actually, it is a little cleaner to recognise the more general pattern here, and
define the functions as strict folds on `ℕ`:

```agda
foldr-ℕ : (A → A) → A → ℕ → A
foldr-ℕ f b zero    = b
foldr-ℕ f b (suc n) = f (foldr-ℕ f b n)

foldl-ℕ-go : (A → A) → ℕ → A → A
foldl-ℕ-go f zero    x = x
foldl-ℕ-go f (suc n) x = foldl-ℕ-go f n $! f x

foldl-ℕ : (A → A) → A → ℕ → A
foldl-ℕ f x n = foldl-ℕ-go f n $! x
```

Then we can prove that both the strict and lazy forms of these functions are
equivalent:

```agda
f-comm : ∀ (f : A → A) x n → f (foldr-ℕ f x n) ≡ foldr-ℕ f (f x) n
f-comm f x zero    i = f x
f-comm f x (suc n) i = f (f-comm f x n i)

foldl-ℕ-foldr : ∀ f (x : A) n → foldr-ℕ f x n ≡ foldl-ℕ f x n
foldl-ℕ-foldr f x zero    = sym ($!-≡ (foldl-ℕ-go f zero) x)
foldl-ℕ-foldr f x (suc n) = f-comm f x n 
                          ; foldl-ℕ-foldr f (f x) n 
                          ; sym ($!-≡ (foldl-ℕ-go f (suc n)) x)
```

This means we can define our conversion from the Peano numbers in the strict
form, but prove things about the lazy form.

# Termination

There is a way to convert from `ℕ` that is faster still: we could rely on Agda's
built-in `div` and `mod` functions to avoid the `inc` step altogether.

```agda
⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ =
  if even n
  then 1ᵇ ⟦ n ÷ 2 ⇑⟧
  else 2ᵇ ⟦ n ÷ 2 ⇑⟧
```

This is asymptotically faster than any implementation which uses `inc`: however
it doesn't pass the termination checker.
As of yet, I haven't figured out how to get it to pass the termination checker
without incurring a serious performance penalty.

# Operations

## Addition

Now we need to encode the different desired operations on the binary numbers.
Addition is first: we can write a naive version of this function by just
expanding the definition of addition and definition of the binary numbers.

```
0           + y           = y

x           + 0           = x

(1 + 2 * x) + (1 + 2 * y) = 2 + 2 * (x + y)

(1 + 2 * x) + (2 + 2 * y) = 3 + 2 * (x + y)
                          = 1 + (2 + 2 * (x + y))

(2 + 2 * x) + (1 + 2 * y) = 3 + 2 * (x + y)
                          = 1 + (2 + 2 * (x + y))

(2 + 2 * x) + (2 + 2 * y) = 4 + 2 * (x + y)
                          = 2 + 2 * (1 + x + y)
```

Translated into Agda the above looks like the following:

```agda
_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    + ys    = ys
xs    + 0ᵇ    = xs
1ᵇ xs + 1ᵇ ys = 2ᵇ (xs + ys)
1ᵇ xs + 2ᵇ ys = inc (2ᵇ (xs + ys))
2ᵇ xs + 1ᵇ ys = inc (2ᵇ (xs + ys))
2ᵇ xs + 2ᵇ ys = 2ᵇ inc (xs + ys)
```

Unfortunately this is nowhere near as efficient as it could be: we're calling
`inc` a bunch of times on the output of the recursive call, when we should be
using carrying to do the whole thing in one pass.
That does make the function a lot longer, but it is much faster:

<details>
<summary>Full Addition Implementation</summary>

```agda
add₁ : 𝔹 → 𝔹 → 𝔹
add₂ : 𝔹 → 𝔹 → 𝔹

add₁ 0ᵇ      ys      = inc ys
add₁ (1ᵇ xs) 0ᵇ      = 2ᵇ xs
add₁ (2ᵇ xs) 0ᵇ      = 1ᵇ inc xs
add₁ (1ᵇ xs) (1ᵇ ys) = 1ᵇ add₁ xs ys
add₁ (1ᵇ xs) (2ᵇ ys) = 2ᵇ add₁ xs ys
add₁ (2ᵇ xs) (1ᵇ ys) = 2ᵇ add₁ xs ys
add₁ (2ᵇ xs) (2ᵇ ys) = 1ᵇ add₂ xs ys

add₂ 0ᵇ      0ᵇ      = 2ᵇ 0ᵇ
add₂ 0ᵇ      (1ᵇ ys) = 1ᵇ inc ys
add₂ 0ᵇ      (2ᵇ ys) = 2ᵇ inc ys
add₂ (1ᵇ xs) 0ᵇ      = 1ᵇ inc xs
add₂ (2ᵇ xs) 0ᵇ      = 2ᵇ inc xs
add₂ (1ᵇ xs) (1ᵇ ys) = 2ᵇ add₁ xs ys
add₂ (1ᵇ xs) (2ᵇ ys) = 1ᵇ add₂ xs ys
add₂ (2ᵇ xs) (1ᵇ ys) = 1ᵇ add₂ xs ys
add₂ (2ᵇ xs) (2ᵇ ys) = 2ᵇ add₂ xs ys

infixl 6 _+_
_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    + ys    = ys
1ᵇ xs + 0ᵇ    = 1ᵇ xs
2ᵇ xs + 0ᵇ    = 2ᵇ xs
1ᵇ xs + 1ᵇ ys = 2ᵇ (xs + ys)
1ᵇ xs + 2ᵇ ys = 1ᵇ add₁ xs ys
2ᵇ xs + 1ᵇ ys = 1ᵇ add₁ xs ys
2ᵇ xs + 2ᵇ ys = 2ᵇ add₁ xs ys
```
</details>

## Multiplication

Multiplication of binary numbers is actually one of the most well-studied
algorithms out there: the standard encoding will get you an $\mathcal{O}(n^2)$
(where $n$ is the number of bits) algorithm, but there are actually some
reasonably easy-to-implement algorithms (Karatsuba multiplication being the most
prominent) that can improve on that bound.
In fact, in 2019 an $\mathcal{O}(n \log n)$ algorithm was discovered: whether or
not such an algorithm existed was an important open question in computer
science.

Now, Karatsuba multiplication is actually a relatively simple algorithm, but it
only actually gets a speedup when the numbers being multiplied have much more
than 300 bits.
For our purposes (a general-purpose number type to replace the peano numbers in
Agda), we're probably better off with just the standard long multiplication.

```agda
double : 𝔹 → 𝔹
double 0ᵇ = 0ᵇ
double (1ᵇ xs) = 2ᵇ double xs
double (2ᵇ xs) = 2ᵇ 1ᵇ xs

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    * ys = 0ᵇ
1ᵇ xs * ys = ys + double (ys * xs)
2ᵇ xs * ys = double (ys + ys * xs)
```

## Subtraction

<details>
<summary>Subtraction</summary>

```agda
dec′ : 𝔹 → 𝔹
dec : 𝔹 → 𝔹

dec′ 0ᵇ = 0ᵇ
dec′ (1ᵇ xs) = 2ᵇ dec′ xs
dec′ (2ᵇ xs) = 2ᵇ 1ᵇ xs

dec 0ᵇ = 0ᵇ
dec (2ᵇ xs) = 1ᵇ xs
dec (1ᵇ xs) = dec′ xs

ones : ℕ → 𝔹 → 𝔹
ones zero    xs = xs
ones (suc n) xs = ones n (1ᵇ xs)

push : 𝔹 → 𝔹 → 𝔹
push 0ᵇ     xs      = xs
push (2ᵇ t) xs      = push t (2ᵇ xs)
push (1ᵇ t) 0ᵇ      = push t 0ᵇ
push (1ᵇ t) (1ᵇ xs) = push t (1ᵇ xs)
push (1ᵇ t) (2ᵇ xs) = push t (2ᵇ 1ᵇ xs)

sub₄ : ℕ → 𝔹 → 𝔹 → 𝔹 → 𝔹
sub₃ : ℕ → 𝔹 → 𝔹 → 𝔹 → 𝔹

sub₄ n t 0ᵇ         ys      = 0ᵇ
sub₄ n t (1ᵇ xs)    (1ᵇ ys) = sub₄ n (2ᵇ t) xs ys
sub₄ n t (1ᵇ xs)    (2ᵇ ys) = sub₄ n (1ᵇ t) xs ys
sub₄ n t (1ᵇ xs)    0ᵇ      = ones n (push (1ᵇ t) (dec′ xs))
sub₄ n t (2ᵇ xs)    (2ᵇ ys) = sub₄ n (2ᵇ t) xs ys
sub₄ n t (2ᵇ xs)    (1ᵇ ys) = sub₃ n (1ᵇ t) xs ys
sub₄ n t (2ᵇ xs)    0ᵇ      = ones n (push (2ᵇ t) (dec′ xs))

sub₃ n t 0ᵇ      0ᵇ      = ones n (push t 0ᵇ)
sub₃ n t 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₃ n t 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₃ n t (1ᵇ xs) 0ᵇ      = ones n (push t (2ᵇ dec′ xs))
sub₃ n t (2ᵇ xs) 0ᵇ      = ones n (push t (2ᵇ 1ᵇ xs))
sub₃ n t (1ᵇ xs) (1ᵇ ys) = sub₃ n (1ᵇ t) xs ys
sub₃ n t (2ᵇ xs) (2ᵇ ys) = sub₃ n (1ᵇ t) xs ys
sub₃ n t (1ᵇ xs) (2ᵇ ys) = sub₄ n (2ᵇ t) xs ys
sub₃ n t (2ᵇ xs) (1ᵇ ys) = sub₃ n (2ᵇ t) xs ys

sub₂ : ℕ → 𝔹 → 𝔹 → 𝔹
sub₂ t 0ᵇ      ys      = 0ᵇ
sub₂ t (1ᵇ xs) 0ᵇ      = ones t (dec′ xs)
sub₂ t (2ᵇ xs) 0ᵇ      = ones t (1ᵇ xs)
sub₂ t (1ᵇ xs) (1ᵇ ys) = sub₂ (suc t) xs ys
sub₂ t (2ᵇ xs) (2ᵇ ys) = sub₂ (suc t) xs ys
sub₂ t (1ᵇ xs) (2ᵇ ys) = sub₄ t 0ᵇ xs ys
sub₂ t (2ᵇ xs) (1ᵇ ys) = sub₃ t 0ᵇ xs ys

sub₁ : ℕ → 𝔹 → 𝔹 → 𝔹
sub₁ t xs      0ᵇ      = ones t xs
sub₁ t 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₁ t 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₁ t (1ᵇ xs) (1ᵇ ys) = sub₃ t 0ᵇ xs ys
sub₁ t (2ᵇ xs) (2ᵇ ys) = sub₃ t 0ᵇ xs ys
sub₁ t (2ᵇ xs) (1ᵇ ys) = sub₁ (suc t) xs ys
sub₁ t (1ᵇ xs) (2ᵇ ys) = sub₂ (suc t) xs ys

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
_-_ = sub₁ zero
```
</details>

# Testing Performance
