---
title: Solving Polynomials
tags: Agda
bibliography: Horner's Rule.bib
---

There's a particular function on lists that I'm a little obsessed with:

```haskell
(<.>) :: [a] -> [b] -> [[(a,b)]]
_ <.> [] = []
xs <.> (yh:ys) = foldr f [] xs
  where
    f x zs = [(x,yh)] : foldr (g x) id ys zs
    g x y a (z:zs) = ((x, y) : z) : a zs
    g x y a [] = [(x, y)] : a []
```

It's an implementation of discrete convolution on lists.
[Previously](2017-10-13-convolutions-and-semirings.html) I discussed it in
relation to search patterns: it corresponds (somewhat) to breadth-first search
(rather than depth-first).

Here though, I want to talk about its more traditional interpretation: the
multiplication of two polynomials. Indeed, if you write out your polynomial
backwards:

\begin{align}
&   &   & 2x^2 & + & x    & - &   & 4    & \\
& = &   & 2x^2 & + & 1x^1 & + & - & 4x^0 &  \{ \text{With explicit powers of $x$} \} \\
& = & - & 4x^0 & + & 1x^1 & + &   & 2x^2 & \{ \text{Reversed} \}
\end{align}

You can write the exponents in a list:

```haskell
[-4,1,2]
```

And you can multiply them as so:

```haskell
>>> [-4,1,2] <.> [-4,1,2]
[[(-4,-4)],[(-4,1),(1,-4)],[(-4,2),(1,1),(2,-4)],[(1,2),(2,1)],[(2,2)]]
```

Although the output isn't what we're looking for: that's because it's in a
somewhat sum-of-products form. We can get it back to something readable like so:

```haskell
>>> run = map (sum . map (uncurry (*)))
>>> run ([-4,1,2] <.> [-4,1,2])
[16,-8,-15,4,4]
```

Which is exactly what we want:

$$16 - 8x -15x^2 + 4x^3 + 4x^4$$

# So What's The Use?

This operation on lists, along with its companion in the form of addition:

```haskell
(<+>) :: [a] -> [a] -> [[a]]
[] <+> ys = map pure ys
xs <+> [] = map pure xs
(x:xs) <+> (y:ys) = [x,y] : (xs <+> ys)
```

allow us to interpret lists as polynomials. This kind of thing has a number of
uses, but for now I'm interested in the "freeness" of this representation. I'm
going to be a bit fast and loose with the definitions here, but bear with me:
free objects are "minimal" examples of some class (class can indeed be a Haskell
class here, but it's more general). The classic example is lists:

```haskell
data List a = Nil | Cons a (List a)
```

These are the free monoid[^Haskell-free-monoid]: it's the *simplest* type which
adds monoid operations to some `a`. In other words, you can combine lists in an
associative way:

[^Haskell-free-monoid]: Technically speaking, they're
    [not](http://comonad.com/reader/2015/free-monoids-in-haskell/) free monoids
    in the presence of $\bot$.

```haskell
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)
-- xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
```

You also get an "empty" element:

```haskell
empty = Nil
-- empty ++ xs == xs
-- xs ++ empty = xs
```

And you get *nothing else*. One could imagine a class of commutative monoids,
for instance, which adds commutativity to the requirement of associativity: any
free monoid should not be a member of this class, as they'd no longer be a
"minimal" monoid, because they supported an extra law. In short, free objects of
some class are those which:

#. Obey the laws of the class.
#. Do not obey any further laws which can't be derived from the laws of the
   class.

We'll need two more things:

```haskell
pure :: forall a.             a -> List a
fold :: forall m. Monoid m => List m -> m
```

`pure`{.haskell} here is indeed the same pure as the one from
`Applicative`{.haskell}, but that's just a coincidence, I'm afraid---we won't be
using it for anything applicative-y today.

These two functions will allow us to treat lists as a little language for monoid
expressions. `pure` will give us variables, and `fold`{.haskell} will let us
execute the AST.

The correctness of this language is ensured by the fact that `fold` is a
*homomorphism*. This means it follows the laws:

```haskell
fold (xs ++ ys) == fold xs <> fold ys
fold [] == mempty
```

In other words, it doesn't make a difference if you use the monoid operations on
lists and then `fold`, or if you `fold` and then use the monoid operations
on the result: you'll still get the same answer.

# No Really, What's The Use?

Yeah, yeah. Well, free objects in combination with homomorphisms are probably
most well-known in Haskell in the context of "extensible effects"
[@kiselyov_extensible_2013-2].

Here, though, we're going to use the "AST" way of looking at things to prove
equality of equations written in the class of the free object.

In Agda, you have two notions of equality. Definitional equality is the more
superficial of the two: if two expressions *look* equal, they are.

```agda
x + y ≡ x + y
```

Well, it goes a little further than that: it will run functions to normal form,
without looking under a lambda. That's why, with the following definition of
`+`:

```agda
_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)
```

The first function here will typecheck, and the second will not:

```agda
+-identityˡ : ∀ x → 0 + x ≡ x
+-identityˡ _ = refl

+-identityʳ : ∀ x → x + 0 ≡ x
+-identityʳ _ = refl
```

We *can* get the second to typecheck, though, like so:

```agda
+-identityʳ : ∀ x → x + 0 ≡ x
+-identityʳ zero = refl
+-identityʳ (suc x) = cong suc (+-identityʳ x)
```

We just need to hold Agda's hand, showing it that all cases do indeed result in
the correct answer.

This gets tedious, fast, especially when there are lots of variables involved.
Consider:

```agda
prop : ∀ w x y z →  w ∙ (((x ∙ ε) ∙ y) ∙ z) ≈ (w ∙ x) ∙ (y ∙ z)
```

The proof is ugly and mechanical:

```agda
prop : ∀ w x y z →  w ∙ (((x ∙ ε) ∙ y) ∙ z) ≈ (w ∙ x) ∙ (y ∙ z)
prop w x y z =
  (refl ⟨ ∙-cong ⟩ assoc (x ∙ ε) y z)
    ⟨ trans ⟩
  (sym (assoc w (x ∙ ε) (y ∙ z)))
    ⟨ trans ⟩
  (refl ⟨ ∙-cong ⟩ identityʳ x ⟨ ∙-cong ⟩ refl)
```

We know it's true, because `∙` is associative, so parentheses don't matter, and
`ε` is the empty value, so it doesn't affect anything, but it's difficult to
convince the compiler of that fact. Like the examples with `+` above, the `∙`
may rely on the values of its arguments to run, so Agda can't go any further
with the expression.

Here's where lists come in: they don't rely on their contents *at all* for the
monoid operations (otherwise they wouldn't be free monoids), so they can run all
they like. In fact:


```agda
prop : ∀ {a} {A : Set a} {w x y z : A}
     →  [ w ] ++ ((([ x ] ++ []) ++ [ y ]) ++ [ z ])
     ≡ ([ w ] ++ [ x ]) ++ ([ y ] ++ [ z ])
prop = refl
```

Effectively, lists are a normal form for expressions over monoids: if the two
normalized expressions are equal, then the expressions themselves must be equal.
In combination with the homomorphism, this can be used to make an automatic
solver. The implementation is a little weird, but once done you can write stuff
like this:

```agda
prop : ∀ w x y z → w ∙ (((x ∙ ε) ∙ y) ∙ z) ≈ (w ∙ x) ∙ (y ∙ z)
prop = solve 4
  (λ w x y z →  w ⊕ (((x ⊕ id) ⊕ y) ⊕ z) ⊜ (w ⊕ x) ⊕ (y ⊕ z))
  refl
```

As it turns out, where lists exhibit this normalizing behaviour for monoids,
polynomials (as described above) exhibit the same behaviour for *rings*.

# Implementing a Ring Solver

Agda [has a ring
solver](https://agda.github.io/agda-stdlib/Algebra.Solver.Ring.html) in the
standard library already, which we'll be using a little to help our
implementation. Mainly, though, we'll use "Proving Equalities in a Commutative
Ring Done Right in Coq" [@hutchison_proving_2005]. First things first, then, we
need to nail down the representation we're going to use.

# Horner Normal Form

Our first stab at a representation will start off like this:

```agda
open import Algebra

module Polynomials {a} (coeff : RawRing a) where

open RawRing coeff
```

The entire module is parameterized over whatever ring we'll end up using:
`Carrier` is the type of the ring itself. In Haskell, this kind of thing might
use a type class: here, we pass in a record which contains the type, functions,
and laws we're interested in. This makes it easier to swap in different rings
for the same type, and it's the standard Agda way of doing things. The `RawRing`
type is just a record, defined like this:

```agda
record RawRing c : Set (suc c) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier : Set c
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
```

`Raw` refers to the fact that it doesn't carry any proofs. `Op₂ A` is a type
synonym for `A → A → A`.

Now, for the actual functions:

```agda
open import Data.List as List using (List; _∷_; [])

Poly : Set a
Poly = List Carrier

_⊞_ : Poly → Poly → Poly
[] ⊞ ys = ys
(x ∷ xs) ⊞ [] = x ∷ xs
(x ∷ xs) ⊞ (y ∷ ys) = x + y ∷ xs ⊞ ys

_⊠_ : Poly → Poly → Poly
[] ⊠ ys = []
(x ∷ xs) ⊠ [] = []
(x ∷ xs) ⊠ (y ∷ ys) =
  x * y ∷ (List.map (x *_) ys ⊞ (xs ⊠ (y ∷ ys)))
```


# Gaps

As it stands, the above representation has two problems:

Redundancy

:   The representation suffers from the problem of trailing zeroes. In other
    words, the polynomial $2x$ could be represented by any of the following:
  
    ```agda
    [0, 2]
    [0, 2, 0]
    [0, 2, 0, 0]
    [0, 2, 0, 0, 0, 0, 0]
    ```
    
    This is a problem for a solver: the whole *point* is that equivalent
    expressions are represented the same way.

Inefficiency

:   Expressions will tend to have large gaps, full only of zeroes. Something
    like $x^5$ will be represented as a list with 6 elements, only the last one
    being of interest. Since addition is linear in the length of the list, and
    multiplication quadratic, this is a major concern.

In the Coq implementation [@hutchison_proving_2005], the problem is addressed
primarily from the efficiency perspective: they add a field for the "power
index". For our case, we'll just store a list of pairs, where the second element
of the pair is the power index.

A brief aside: in the paper, the following power index:

```agda
(c , i) ∷ P
```

Is said to be the representation of:

$$ P \times X^i + c $$

This didn't make a huge amount of sense to me, though. Since we're representing
the preceding gap, I decided to go with the following translation:

$$ (P \times X + c) * X^i $$

By way of example, the polynomial:

$$ 3 + 2x² + 4x⁵ + 2x⁷ $$

Will be represented as:

```agda
[(3,0),(2,1),(4,2),(2,1)]
```

Or, mathematically:

$$ x^0 (3 + x x^1 (2 + x x^2 * (4 + x x^1 (2 + x 0)))) $$


Also, we can kill two birds with one stone here: if we disallow zeroes
*entirely* in the list, we lose the gaps, and we also get a unique
representation. Finally, we have a representation:

```agda
infixr 5 0≠_
record Coeff : Set (a ⊔ ℓ) where
  inductive
  constructor 0≠_
  field
    coeff : Carrier
    .{coeff≠0} : ¬ Zero-C coeff

Poly : Set (a ⊔ ℓ)
Poly = List (Coeff × ℕ)
```

The coefficients are ensured to be nonzero, as promised. We allow the user to
supply an "Is zero" property, which is what we use to ensure every coefficient
is indeed not zero. I've also marked the proof as irrelevant (that's the dot
before it), so that it's not computed at runtime.

To make things easier, we can define a normalizing variant of `∷`:

```agda
infixr 8 _⍓_
_⍓_ : Poly → ℕ → Poly
[] ⍓ i = []
((x , j) ∷ xs) ⍓ i = (x , j ℕ.+ i) ∷ xs

infixr 5 _∷↓_
_∷↓_ : (Carrier × ℕ) → Poly → Poly
(x , i) ∷↓ xs with zero-c? x
... | yes p = xs ⍓ suc i
... | no ¬p = (0≠_ x {¬p} , i) ∷ xs
```

# Addition

Our addition and multiplication functions will need to properly deal with the
new gapless formulation. First things first, we'll need a way to match the power
indices. We can use a function from @mcbride_view_2004 to do so:

```agda
data Ordering : ℕ → ℕ → Set where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

compare : ∀ m n → Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
compare (suc .m)           (suc .(suc m + k)) | less    m k = less    (suc m) k
compare (suc .m)           (suc .m)           | equal   m   = equal   (suc m)
compare (suc .(suc m + k)) (suc .m)           | greater m k = greater (suc m) kv
```

This is a classic example of a "leftist" function: after pattern matching on
one of the constructors of `Ordering`, it gives you information on type
variables to the *left* of the pattern. In other words, when you run the
function on some variables, the result of the function will give you
information on its arguments.

# Suspicion

While the gapless representation is *meant* to be more efficient, that compare
function is linear in the size of its smaller argument, so I don't see
how---with peano numbers, at any rate---we have actually improved complexity.
We've definitely reduced the number of operations on the underlying semiring,
and there may be efficiency gains elsewhere (multiplication seems a good bit
faster), but I wonder if there's a way to use a more efficient version of
`compare`?

There are
[seven](https://agda.readthedocs.io/en/v2.5.4/language/built-ins.html#functions-on-natural-numbers)
functions on natural numbers which Agda will replace with their equivalents on
Haskell's `Integer`. The three of interest here are:

```agda
_-_ : N → ℕ → ℕ
n     - zero  = n
zero  - suc m = zero
suc n - suc m = n - m
{-# BUILTIN NATMINUS _-_ #-}

_==_ : ℕ → ℕ → Bool
zero  == zero  = true
suc n == suc m = n == m
_     == _     = false
{-# BUILTIN NATEQUALS _==_ #-}

_<_ : ℕ → ℕ → Bool
_     < zero  = false
zero  < suc _ = true
suc n < suc m = n < m
{-# BUILTIN NATLESS _<_ #-}
```

The implementation you see is kind of a lie: at runtime, those functions are
replaced by their faster, unverified implementations. This is good news for us,
though: we can try reimplement `compare` using them, and we should get a much
quicker function. Our first try ends in failure:

```agda
compare : (n m : ℕ) → Ordering n m
compare n m with n < m
compare n m | true = less n (m - n - 1)
compare n m | false with n == m
compare n m | false | false = greater m (n - m - 1)
compare n m | false | true = equal m
```

Agda complains:

> `suc (n + (m - n - 1)) != m of type ℕ`

Hmm. Evidently, we need to prove something. Here's what that proof might look
like:

```agda
less-hom : ∀ n m → ((n < m) ≡ true) → m ≡ suc (n + (m - n - 1))
less-hom zero zero ()
less-hom zero (suc m) _ = refl
less-hom (suc n) zero ()
less-hom (suc n) (suc m) n<m = cong suc (less-hom n m n<m)
```

Wait---have we just given up efficiency here? Well, no, because we can
[*erase*](https://agda.github.io/agda-stdlib/Relation.Binary.PropositionalEquality.TrustMe.html)
the proof, which hopefully mean it isn't computed at runtime:

```agda
eq-hom : ∀ n m → ((n == m) ≡ true) → n ≡ m
eq-hom zero zero _ = refl
eq-hom zero (suc m) ()
eq-hom (suc n) zero ()
eq-hom (suc n) (suc m) n≡m = cong suc (eq-hom n m n≡m)

gt-hom : ∀ n m → ((n < m) ≡ false) → ((n == m) ≡ false) → n ≡ suc (m + (n - m - 1))
gt-hom zero zero n<m ()
gt-hom zero (suc m) () n≡m
gt-hom (suc n) zero n<m n≡m = refl
gt-hom (suc n) (suc m) n<m n≡m = cong suc (gt-hom n m n<m n≡m)

compare : (n m : ℕ) → Ordering n m
compare n m with n < m  | inspect (_<_ n) m
... | true  | [ n<m ] rewrite erase (less-hom n m n<m) = less n (m - n - 1)
... | false | [ n≮m ] with n == m | inspect (_==_ n) m
... | true  | [ n≡m ] rewrite erase (eq-hom n m n≡m) = equal m
... | false | [ n≢m ] rewrite erase (gt-hom n m n≮m n≢m) = greater m (n - m - 1)
```

# Termination & Redundancy

Totality and nontermination isn't actually a problem I've encountered much in
Agda, but it does occasionally come up. Even when it does, the complaints often
(not always, but often) point towards redundancy, rather than necessary
complexity. For instance, the straightforward translation of `⊞` doesn't pass:

```agda
_⊞_ : Poly → Poly → Poly
_⊞_ [] ys = ys
_⊞_ (x ∷ xs) [] = x ∷ xs
_⊞_ ((x , i) ∷ xs) ((y , j) ∷ ys) with compare i j
... | less    .i k = (x , i) ∷ xs ⊞ ((y , k) ∷ ys)
... | equal   .i   = (coeff x + coeff y , i) ∷↓ (xs ⊞ ys)
... | greater .j k = (y , j) ∷ ((x , k) ∷ xs) ⊞ ys
```

Why? Well because the arguments passed in the recursive calls aren't strictly
smaller---or, at least, Agda can't see that they are. You see, *we* know that
(for instance) the `k` passed in is smaller than the `j` before it, but it's not
trivial to show that, so Agda complains.

One trick to make termination more obvious is to eliminate any redundancy in
the code. For instance, the first clause above checks if the left-hand-side list
is empty: but when we call back to the function in the `greater` clause, we
should be able to skip that check. Here's the strategy: split every clause which
checks for some condition into its own function, and then call the correct
function when you know a condition must be passed. 

```agda
mutual
  infixl 6 _⊞_
  _⊞_ : Poly → Poly → Poly
  [] ⊞ ys = ys
  ((x , i) ∷ xs) ⊞ ys = ⊞-zip-r x i xs ys

  ⊞-zip-r : Coeff → ℕ → Poly → Poly → Poly
  ⊞-zip-r x i xs [] = (x , i) ∷ xs
  ⊞-zip-r x i xs ((y , j) ∷ ys) = ⊞-zip (compare i j) x xs y ys

  ⊞-zip : ∀ {p q}
        → Ordering p q
        → Coeff
        → Poly
        → Coeff
        → Poly
        → Poly
  ⊞-zip (less    i k) x xs y ys = (x , i) ∷ ⊞-zip-r y k ys xs
  ⊞-zip (greater j k) x xs y ys = (y , j) ∷ ⊞-zip-r x k xs ys
  ⊞-zip (equal   i  ) (0≠ x) xs (0≠ y) ys =
    (x + y , i) ∷↓ (xs ⊞ ys)
```

And it works! This function is structurally terminating. You'll notice that
effectively every sum type gets its own function: the first only checks if its
left argument is cons or nil, the second its right, and the third checks the
result of the comparison. This should also make the function more efficient:
we're effectively manually performing call-pattern specialization
[@jones_call-pattern_2007]. I wonder if that optimization can be used in the
termination checker?

# Multiplication

The version of multiplication I began this article with was an inlined version
of shift and add. What I'm going to write here is the same, but not inlined:
this will allow us to use `⊞` in the definition, and consequently, in the
proofs:

```agda
infixl 7 _⋊_
_⋊_ : Carrier → Poly → Poly
_⋊_ x = foldr ⋊-step []
  where
  ⋊-step : Coeff × ℕ → Poly → Poly
  ⋊-step (0≠ y , i) ys = (x * y , i) ∷↓ ys

infixl 7 _⊠_
_⊠_ : Poly → Poly → Poly
xs ⊠ [] = []
xs ⊠ ((0≠ y , j) ∷ ys) = foldr ⊠-step [] xs ⍓ j
  where
  ⊠-step : Coeff × ℕ → Poly → Poly
  ⊠-step (0≠ x , i) xs = (x * y , i) ∷↓ (x ⋊ ys ⊞ xs ⊠ ys)
```

# Binary

Before we continue with the polynomials, we can take a brief detour to talk
about binary numbers in proof assistants. Quite often a list of booleans will be
used (instead of the normal Peano encoding) to improve the efficiency of
manipulation, while maintaining some of the ability to write proofs. Also, some
[data structures mimic the structure of binary
numbers](2017-04-23-verifying-data-structures-in-haskell-lhs.html), meaning that
the proofs can often carry over.

One of the problems that shows up in implementations is the same as our problem
above: redundant zeroes. There are a
[number](https://lists.chalmers.se/pipermail/agda/2018/010379.html) of
[ways](http://www.botik.ru/pub/local/Mechveliani/binNat/) to get around this,
but here we see a pleasingly simple one: represent it as a sparse polynomial!
There's no need for pairs, since there's only one possible coefficient (1, since
we've disallowed zeroes). So all we have instead is a list of the number of
zeroes between each 1:

```agda
0  = []
52 = 001011 = [2,1,0]
4  = 001    = [2]
5  = 101    = [0,1]
10 = 0101   = [1,1]

Bin : Set
Bin = List ℕ
```

These are unique representations, and the functions on them are quite simple:

```agda
incr′ : ℕ → Bin → Bin
incr″ : ℕ → ℕ → Bin → Bin

incr′ i [] = i ∷ []
incr′ i (x ∷ xs) = incr″ i x xs

incr″ i zero xs = incr′ (suc i) xs
incr″ i (suc x) xs = i ∷ x ∷ xs

incr : Bin → Bin
incr = incr′ 0

infixl 6 _+_
_+_ : Bin → Bin → Bin
[] + ys = ys
(x ∷ xs) + ys = +-zip-r x xs ys
  where
  +-zip   :     ∀ {x y} → Ordering x y → Bin → Bin → Bin
  ∔-zip   : ℕ → ∀ {i j} → Ordering i j → Bin → Bin → Bin
  +-zip-r :     ℕ → Bin → Bin → Bin
  ∔-zip-r : ℕ → ℕ → Bin → Bin → Bin
  ∔-cin   : ℕ → Bin → Bin → Bin
  ∔-zip-c : ℕ → ℕ → ℕ → Bin → Bin → Bin

  +-zip (less    i k) xs ys = i ∷ +-zip-r k ys xs
  +-zip (equal   k  ) xs ys = ∔-cin (suc k) xs ys
  +-zip (greater j k) xs ys = j ∷ +-zip-r k xs ys

  +-zip-r x xs [] = x ∷ xs
  +-zip-r x xs (y ∷ ys) = +-zip (compare x y) xs ys

  ∔-cin i [] = incr′ i
  ∔-cin i (x ∷ xs) = ∔-zip-r i x xs

  ∔-zip-r i x xs [] = incr″ i x xs
  ∔-zip-r i x xs (y ∷ ys) = ∔-zip i (compare y x) ys xs

  ∔-zip-c c zero k xs ys = ∔-zip-r (suc c) k xs ys
  ∔-zip-c c (suc i) k xs ys = c ∷ i ∷ +-zip-r k xs ys

  ∔-zip c (less    i k) xs ys = ∔-zip-c c i k ys xs
  ∔-zip c (greater j k) xs ys = ∔-zip-c c j k xs ys
  ∔-zip c (equal     k) xs ys = c ∷ ∔-cin k xs ys

pow : ℕ → Bin → Bin
pow i [] = []
pow i (x ∷ xs) = (x ℕ.+ i) ∷ xs

infixl 7 _*_
_*_ : Bin → Bin → Bin
_*_ [] _ = []
_*_ (x ∷ xs) = pow x ∘ foldr (λ y ys → y ∷ xs + ys) []
```

# Multivariate Polynomials

Up until now our polynomial has been an expression in just one variable. For it
to be truly useful, though, we'd like to be able to extend it to many: luckily
there's a well-known isomorphism we can use to extend our earlier
implementation. A multivariate polynomial is one where its coefficients are
polynomials with one fewer variable [@cheng_functional_2018]. In Agda, this
looks like the following:

```agda
mutual
  Poly : ℕ → Set ℓ
  Poly zero = Lift ℓ Carrier
  Poly (suc n) = Coeffs n

  Coeffs : ℕ → Set ℓ
  Coeffs n = List (Coeff n × ℕ)

  infixr 5 0≠_
  record Coeff (n : ℕ) : Set ℓ where
    inductive
    constructor 0≠_
    field
      poly : Poly n
      .{poly≠0} : ¬ Zero n poly

  Zero : ∀ n → Poly n → Set ℓ
  Zero zero (lift x) = Zero-C x
  Zero (suc n) [] = Lift ℓ ⊤
  Zero (suc n) (x ∷ xs) = Lift ℓ ⊥
```

The addition function looks similar to before, with an extra first helper to
check if the polynomial is constant:

```agda
mutual
  infixl 6 _⊞_
  _⊞_ : ∀ {n} → Poly n → Poly n → Poly n
  _⊞_ {zero} (lift x) (lift y) = lift (x + y)
  _⊞_ {suc n} = ⊞-coeffs

  ⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
  ⊞-coeffs [] ys = ys
  ⊞-coeffs ((x , i) ∷ xs) ys = ⊞-zip-r x i xs ys

  ⊞-zip-r : ∀ {n} → Coeff n → ℕ → Coeffs n → Coeffs n → Coeffs n
  ⊞-zip-r x i xs [] = (x , i) ∷ xs
  ⊞-zip-r x i xs ((y , j) ∷ ys) = ⊞-zip (compare i j) x xs y ys

  ⊞-zip : ∀ {p q n}
        → Ordering p q
        → (x : Coeff n)
        → Coeffs n
        → (y : Coeff n)
        → Coeffs n
        → Coeffs n
  ⊞-zip (less    i k) x xs y ys = (x , i) ∷ ⊞-zip-r y k ys xs
  ⊞-zip (greater j k) x xs y ys = (y , j) ∷ ⊞-zip-r x k xs ys
  ⊞-zip (equal   i  ) (0≠ x) xs (0≠ y) ys =
    (x ⊞ y , i) ∷↓ (⊞-coeffs xs ys)
```

However, there is opportunity for optimization here, as again is exploited in
the Coq implementation. We actually have a similar kind of gap for nesting as we
do for exponentiation: consider a polynomial with 4 variables, $W, X, Y, Z$. The
representation will be something like this:

```agda
Poly of [W,X,Y,Z] with coefficients C = 
  Poly of W with coefficients (
    Poly of X with coefficients (
      Poly of Y with coefficients (
        Poly of Z with coefficients C)))
```

Therefore, if we want to represent the expression $Z^2$, we're going to need
three levels of nesting before we get to what we need.

# Gapless Nesting

We'll start by attempting a similar approach to removing the exponent gaps.
Straight away, though, we run into a problem: the poly type is *indexed* by the
number of variables it contains. So the overall type will have to correspond to
the gap size in some way. The direct way to encode that would be something like
this:

```agda
data Poly : ℕ → Set (a ⊔ ℓ) where
  _Π_ : (gap : ℕ) → ∀ {i} → FlatPoly i → Poly (suc (gap ℕ.+ i))
```

Where `FlatPoly` is effectively the gappy type we had earlier. If you actually
tried to use this type, though, you'd run into issues:

```agda
_⊞_ : ∀ {n} → Poly n → Poly n → Poly n
(gap Π x) ⊞ ys = {!!}
```

Try to pattern match on `ys` and you'll get the following error:

> I'm not sure if there should be a case for the constructor `_Π_`,
> because I get stuck when trying to solve the following unification
> problems (inferred index `≟` expected index):
>
> ```agda
>   suc (gap₂ ℕ.+ i₁) ≟ suc (gap₁ ℕ.+ i)
> ```
>
> when checking that the expression ? has type
>
> ```agda
>   Poly (suc (gap ℕ.+ ;i))
> ```

Why aren't you sure, Agda?! There is a case for it! I know there is!

The problem is that Agda is trying to unify something with a *function*, rather
than constructors. Avoiding this problem is known as "Don't touch the green
slime!" [@mcbride_polynomial_2018]:

> When combining prescriptive and descriptive indices, ensure both are in
> constructor form. Exclude defined functions which yield difficult
> unification problems.

So we're going to have to do something else.

# Storing Inequalities

Since all we need to know about the nested polynomial is that it does indeed
have a smaller number of variables than the outer, we can store that fact in a
proof:

```agda
infixl 6 _Π_
record Poly (n : ℕ) : Set (a ⊔ ℓ) where
  inductive
  constructor _Π_
  field
    {i} : ℕ
    flat  : FlatPoly i
    i≤n   : i ≤ n
```

We won't get any of the problems above using this approach, and we can go ahead
with the rest of the implementation. Like with the exponents, we should store a
proof that this nesting structure is as compact as possible: that it's in normal
form. There are two cases when a polynomial isn't in normal form: when it's an
empty list (it could instead be the constant 0), or when it only has one
constant coefficient. We can express this, like with `Zero`, in a function:

```agda
mutual
  infixl 6 _Π_
  record Poly (n : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _Π_
    field
      {i} : ℕ
      flat  : FlatPoly i
      i≤n   : i ≤ n

  data FlatPoly : ℕ → Set (a ⊔ ℓ) where
    Κ : Carrier → FlatPoly 0
    Σ : ∀ {n} → (xs : Coeffs n) → .{xn : Norm xs} → FlatPoly (suc n)

  infixl 6 _Δ_
  record CoeffExp (i : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _Δ_
    field
      coeff : Coeff i
      pow   : ℕ

  Coeffs : ℕ → Set (a ⊔ ℓ)
  Coeffs n = List (CoeffExp n)

  infixl 6 _≠0
  record Coeff (i : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _≠0
    field
      poly : Poly i
      .{poly≠0} : ¬ Zero poly

  Zero : ∀ {n} → Poly n → Set ℓ
  Zero (Κ x       Π _) = Zero-C x
  Zero (Σ []      Π _) = Lift ℓ ⊤
  Zero (Σ (_ ∷ _) Π _) = Lift ℓ ⊥

  Norm : ∀ {i} → Coeffs i → Set
  Norm []                  = ⊥
  Norm (_ Δ zero  ∷ [])    = ⊥
  Norm (_ Δ zero  ∷ _ ∷ _) = ⊤
  Norm (_ Δ suc _ ∷ _)     = ⊤
```

# Choosing the Inequality

There are multiple ways to express `x ≤ y` in Agda: in the standard library,
three of them are defined for natural numbers.

## Option 1: The Standard Way

The first definition of `≤` is as follows:

```agda
data _≤_ : ℕ → ℕ → Set where
   z≤n : ∀ {n}                 → zero  ≤ n
   s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
```

It actually worked fine, for a bit, until I realized that I had actually made
the time complexity *worse* by using this encoding of gaps. To understand why,
remember the addition function above with the gapless exponent encoding. For it to
work, we needed to compare the gaps, and proceed based on that. We'll need to do
a similar comparison on variable counts for this gapless encoding. However, we
don't store the *gaps* now, we store the number of variables in the nested
polynomial. Consider the following sequence of nestings:

```agda
(5 ≤ 6), (4 ≤ 5), (3 ≤ 4), (1 ≤ 3), (0 ≤ 1)
```

The outer polynomial has 6 variables, but it has a gap to its inner polynomial
of 5, and so on. The comparisons will be made on 5, 4, 3, 1, and 0. Like
repeatedly taking the length of the tail of a list, this is quadratic. There
must be a better way.

## Option 2: With Refl

Once you realize we need to be comparing the gaps and not the tails, the third
encoding of `≤` jumps out:

```agda
record _≤″_ (m n : ℕ) : Set where
  constructor less-than-or-equal
  field
    {k}   : ℕ
    proof : m + k ≡ n
```

It stores the gap *right there*: in `k`!

Unfortunately, though, we're still stuck. While you can indeed run your
comparison on `k`, you're not left with much information about the rest. Say,
for instance, you find out that two respective `k`s are equal. What about the
`m`s? Of course, you *can* show that they must be equal as well, but it requires
a proof. Similarly in the less-than or greater-than cases: each time, you need
to show that the information about `k` corresponds to information about `m`.
Again, all of this can be done, but it all requires propositional proofs, which
are messy, and slow. Erasure is an option, but I'm not sure of the correctness
of that approach.

## Option 3

What we really want is to *run* the comparison function on the gap, but get the
result on the tail. Turns out we can do exactly that with the following:

```agda
infix 4 _≤_
data _≤_ (m : ℕ) : ℕ → Set where
  m≤m : m ≤ m
  ≤-s : ∀ {n} → (m≤n : m ≤ n) → m ≤ suc n
```

(This is a rewritten version of `_≤′_` from Data.Nat.Base).

While this structure stores the same information as `_≤_`, it does so by
induction on the *gap*. That structure can be used to write a comparison
function which was linear in the size of the gap (even though it was comparing
the length of the tail):

```agda
data Ordering : ℕ → ℕ → Set where
  less    : ∀ {n m} → n ≤ m → Ordering n (suc m)
  greater : ∀ {n m} → m ≤ n → Ordering (suc n) m
  equal   : ∀ {n}           → Ordering n n

≤-compare : ∀ {i j n}
          → (i≤n : i ≤ n)
          → (j≤n : j ≤ n)
          → Ordering i j
≤-compare m≤m m≤m = equal
≤-compare m≤m (≤-s m≤n) = greater m≤n
≤-compare (≤-s m≤n) m≤m = less m≤n
≤-compare (≤-s i≤n) (≤-s j≤n) = ≤-compare i≤n j≤n
```

A few things to note here:

#. The `≤-compare` function is one of those reassuring ones for which Agda can
automatically fill in the implementation from the type.
#. This function looks somewhat similar to the one for comparing `ℕ` in Data.Nat,
and as a result, the "matching" logic for degree and number of variables began
to look similar.

# Irrelevance and K

I proceeded happily with the new proof, and the functions began to materialize
mechanically. The proofs did, too, until I was asked to prove the following:

```agda
∀ {i n}
→ (x : i ≤ n)
→ (y : i ≤ n)
→ ∀ xs Ρ
→ Σ⟦ xs ⟧ (drop-1 x Ρ) ≈ Σ⟦ xs ⟧ (drop-1 y Ρ)
```

I've already proven that both sides have the same polynomials, and the same
variables. All I needed to do now was show that the `drop-1` functions behaved
the same. These simply drop the gap from the front of the supplied vector, so
the nested polynomial gets the variables it needs.

It seems like it shouldn't be a problem: after all, every inequality proof is
*irrelevant*: its structure is entirely determined by its type. By all
accounts, we should be able to prove something like this:

```agda
irrel : ∀ {i  n}
      → (x : i ≤ n)
      → (y : i ≤ n)
      → x ≡ y
```

If you go ahead and try it, though, with `--without-K` turned on, you'll get the
following error when you try pattern match on `y` in the first line:

```agda
irrel m≤m y = {!!}
irrel (≤-s x) y = {!!}
```

> I'm not sure if there should be a case for the constructor `m≤m`,
> because I get stuck when trying to solve the following unification
> problems (inferred index `≟` expected index):
> ```agda
>   i ≟ i
> ```
> Possible reason why unification failed:
>
> > Cannot eliminate reflexive equation `i = i` of type `ℕ` because K has
>   been disabled.
>
> when checking that the expression ? has type `m≤m ≡ y`

So we're not able to proceed without K, it would seem.

At the same time, I noticed I'd have to prove other, more complex properties
about `≤`, and it was all looking quite daunting, until I realized that I hadn't
had to prove *any* of these things for the exponentiation case: why not? Well
because the precise proofs we needed were given to us, in the result of the
`compare` function. What we got in `≤-compare` were just proofs about the
lengths, when really we should have looked for proofs about the inequalities
themselves.

# Indexed Ordering

So what would a type for comparisons of the inequalities look like? Well, if we
mimic the one for numbers:

```agda
data Ordering : ℕ → ℕ → Set where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) mv
```

We can see that we'll need some notion of `+` for an inequality: as it turns
out, *transitivity* is the function we're looking for.

```agda
infixl 6 _⋈_
_⋈_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
xs ⋈ m≤m = xs
xs ⋈ (≤-s ys) = ≤-s (xs ⋈ ys)
```

With that, we can write the new `Ordering` type:

```agda
data Ordering {n : ℕ} : ∀ {i j}
                      → (i≤n : i ≤ n)
                      → (j≤n : j ≤ n)
                      → Set
                      where
  _<_ : ∀ {i j-1}
      → (i≤j-1 : i ≤ j-1)
      → (j≤n : suc j-1 ≤ n)
      → Ordering (≤-s i≤j-1 ⋈ j≤n) j≤n
  _>_ : ∀ {i-1 j}
      → (i≤n : suc i-1 ≤ n)
      → (j≤i-1 : j ≤ i-1)
      → Ordering i≤n (≤-s j≤i-1 ⋈ i≤n)
  eq : ∀ {i} → (i≤n : i ≤ n) → Ordering i≤n i≤n
```

The compare function (written here as an operator):

```agda
_∺_ : ∀ {i j n}
    → (x : i ≤ n)
    → (y : j ≤ n)
    → Ordering x y
m≤m ∺ m≤m = eq m≤m
m≤m ∺ ≤-s y = m≤m > y
≤-s x ∺ m≤m = x < m≤m
≤-s x ∺ ≤-s y with x ∺ y
≤-s .(≤-s i≤j-1 ⋈ y) ∺ ≤-s y                | i≤j-1 < .y = i≤j-1 < ≤-s y
≤-s x                ∺ ≤-s .(≤-s j≤i-1 ⋈ x) | .x > j≤i-1 = ≤-s x > j≤i-1
≤-s x                ∺ ≤-s .x               | eq .x = eq (≤-s x)
```

Again, closely mimicking the sparse exponent encoding, we'll write a "power" and
normalizing constructor:

```agda
_Π↑_ : ∀ {n m} → Poly n → (suc n ≤ m) → Poly m
(xs Π i≤n) Π↑ n≤m = xs Π (≤-s i≤n ⋈ n≤m)

infixr 4 _Π↓_
_Π↓_ : ∀ {i n} → Coeffs i → suc i ≤ n → Poly n
[]                       Π↓ i≤n = Κ 0# Π z≤n
(x ≠0 Δ zero  ∷ [])      Π↓ i≤n = x Π↑ i≤n
(x₁   Δ zero  ∷ x₂ ∷ xs) Π↓ i≤n = Σ (x₁ Δ zero  ∷ x₂ ∷ xs) Π i≤n
(x    Δ suc j ∷ xs)      Π↓ i≤n = Σ (x  Δ suc j ∷ xs) Π i≤n
```

Finally, we can write our addition (I've omitted the parts which haven't
changed):

```agda
infixl 6 _⊞_
_⊞_ : ∀ {n} → Poly n → Poly n → Poly n
(xs Π i≤n) ⊞ (ys Π j≤n) = ⊞-match (i≤n ∺ j≤n) xs ys

⊞-match : ∀ {i j n}
      → {i≤n : i ≤ n}
      → {j≤n : j ≤ n}
      → Ordering i≤n j≤n
      → FlatPoly i
      → FlatPoly j
      → Poly n
⊞-match (eq i&j≤n)    (Κ x)  (Κ y)  = Κ (x + y)         Π  i&j≤n
⊞-match (eq i&j≤n)    (Σ xs) (Σ ys) = ⊞-coeffs    xs ys Π↓ i&j≤n
⊞-match (i≤j-1 < j≤n)  xs    (Σ ys) = ⊞-inj i≤j-1 xs ys Π↓ j≤n
⊞-match (i≤n > j≤i-1) (Σ xs)  ys    = ⊞-inj j≤i-1 ys xs Π↓ i≤n
```

# Evaluation

For evaluating our polynomials, we'll make use of "Horner's rule": this is just
a simple algorithm that cuts down on the number of multiplications required. In
the gappy encoding, it would have looked like this:

```agda
⟦_⟧ : Poly → Carrier → Carrier
⟦ xs ⟧ ρ = foldr (λ y ys → y + ys * ρ) 0# xs
```

For the gapless, we get the following:

```agda
⟦_⟧ : Poly → Carrier → Carrier
⟦ xs ⟧ ρ = foldr coeff-eval 0# xs
  where
  coeff-eval : Coeff × ℕ → Carrier → Carrier
  coeff-eval (0≠ x , i) xs = (x + xs * ρ) * ρ ^ i
```

Finally, if we want to handle multiple variables, we'll get the following:

```agda
drop : ∀ {i n} → i ≤ n → Vec Carrier n → Vec Carrier i
drop m≤m Ρ = Ρ
drop (≤-s si≤n) (_ ∷ Ρ) = drop si≤n Ρ

vec-uncons : ∀ {n} → Vec Carrier (suc n) → Carrier × Vec Carrier n
vec-uncons (x ∷ xs) = x , xs

drop-1 : ∀ {i n} → suc i ≤ n → Vec Carrier n → Carrier × Vec Carrier i
drop-1 si≤n xs = vec-uncons (drop si≤n xs)

mutual
  Σ⟦_⟧ : ∀ {n} → Coeffs n → (Carrier × Vec Carrier n) → Carrier
  Σ⟦ x ≠0 Δ i ∷ xs ⟧ (ρ , Ρ) = (⟦ x ⟧ Ρ + Σ⟦ xs ⟧ (ρ , Ρ) * ρ) * ρ ^ i
  Σ⟦ [] ⟧ _ = 0#

  ⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
  ⟦ Κ x  Π i≤n ⟧ _ = x
  ⟦ Σ xs Π i≤n ⟧ Ρ = Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
```

We see here again that the choice of inequality was the right one: we only pay
for the amount of the vector that we drop, rather than for the size of the tail,
as we might using another one of the inequalities.

# Writing the Proofs

We're going to prove homomorphism according to some
[setoid](https://en.wikipedia.org/wiki/Setoid): an equivalence relation over
some set. This relation could be propositional equality (for instance), but it's
not necessary: it could instead be something more exotic which we'll see later.

As an equivalence relation, it needs the following three functions:

```agda
-- Reflexivity
refl : ∀ {x} → x ≈ x
-- Symmetry
sym : ∀ {x y} → x ≈ y → y ≈ x
-- Transitivity
trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
```

And, as the type we're working with is a ring, it will need to obey the ring
laws, according to the above relation. For example:

```agda
*-comm : ∀ x y → x * y ≈ y * x
```

There's one more thing: because this is a setoid, you don't get *congruence*
automatically. This means that the user has to supply a further two functions:

```agda
+-cong : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → x₁ + y₁ ≈ x₂ + y₂
*-cong : ∀ {x₁ x₂ y₁ y₂} → x₁ ≈ x₂ → y₁ ≈ y₂ → x₁ * y₁ ≈ x₂ * y₂
```

With all of this stuff, we could go ahead and prove everything we need at this
point. But it's more than a little painful: for instance, we'll need later on a
definition for exponentiation.

```agda
infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n
```

A property we'll rely on is the following familiar identity:

$$ x^i x^j = x^{i + j} $$

A proof of this fact looks like this:

```agda
pow-add : ∀ x i j
        → x ^ i * x ^ j ≈ x ^ (i ℕ.+ j)
pow-add : ∀ x i j → x ^ i * x ^ j ≈ x ^ (i ℕ.+ j)
pow-add x zero j = *-identityˡ (x ^ j)
pow-add x (suc i) j =
  *-assoc x (x ^ i) (x ^ j)
    ⟨ trans ⟩
  (refl ⟨ *-cong ⟩ pow-add x i j)
```

The brackets (`⟨ ⟩`) work like backticks in Haskell: they turn a function with
two arguments into an infix operator.

The issue is that it's hard to see what's going on. First things first, the
pattern "`refl ⟨ *-cong ⟩ prf`" will be used often: basically, it means "apply
`prf` to the right-hand-side of the `*`". To cut down on noise, we can define
some operators to do that for us:

```agda
infixr 1 ≪+_ +≫_ ≪*_ *≫_
≪+_ : ∀ {x₁ x₂ y} → x₁ ≈ x₂ → x₁ + y ≈ x₂ + y
≪+ prf = +-cong prf refl

+≫_ : ∀ {x y₁ y₂} → y₁ ≈ y₂ → x + y₁ ≈ x + y₂
+≫_ = +-cong refl

≪*_ : ∀ {x₁ x₂ y} → x₁ ≈ x₂ → x₁ * y ≈ x₂ * y
≪* prf = *-cong prf refl

*≫_ : ∀ {x y₁ y₂} → y₁ ≈ y₂ → x * y₁ ≈ x * y₂
*≫_ = *-cong refl
```

"`≪+`" means: "apply this proof to the left hand side of the plus". Because
they're right-associative, they can be chained, so if we wanted to drill down
into some large expression, we could write "`≪+ ≪+ *≫ ≪* prf`", which would mean
"to the left of the plus, left again, right of the times, and left of the
times", like directions.

That doesn't solve the real issue, though: the proof is hard to read because we
don't know what's going on inside it. If we were to write it out with a pen and
paper, we'd write the state of the expression after each rewrite along with the
rules we were using to justify it. Luckily, we can do the same in Agda, like so:

```agda
pow-add : ∀ x i j → x ^ i * x ^ j ≈ x ^ (i ℕ.+ j)
pow-add x zero j = *-identityˡ (x ^ j)
pow-add x (suc i) j =
  begin
    x ^ suc i * x ^ j
  ≡⟨⟩
    (x * x ^ i) * x ^ j
  ≈⟨ *-assoc x (x ^ i) (x ^ j) ⟩
    x * (x ^ i * x ^ j)
  ≈⟨ *≫ pow-add x i j ⟩
    x * x ^ (i ℕ.+ j)
  ≡⟨⟩
    x ^ suc (i ℕ.+ j)
  ∎
```

The syntax works like this: `begin` signals the start of the proof, `∎` the end.
In between, you write the state of the expression, interspersed with the rules
that allow you too rewrite it from one form to the next. `≡⟨⟩` is the simplest
rule: you use it when a rewrite is definitionally equal. So on our first
rewrite, we're just using the definition of `^`. Then, `≈⟨ prf ⟩` applies the
equality inside the brackets.

This way of writing proofs is very powerful: it makes what might seem
intractably complex manageable. 

Also, while it may *seem* like this is a special language feature, these are all
actually just normal operators, defined in the standard library.

# List Homomorphism

We use list algebras too make the proofs cleaner.

@mu_algebra_2009

# Setoid

I mentioned that the notion of equality we were using was more general than
propositional, and that we could use it more flexibly in different contexts.

## Tracing

First off, we can look at lists (again). The three things required by an
equivalence relation: reflexivity, transitivity, and symmetry, are all familiar
functions on lists: empty lists, concatenation, and reversal. For propositional
equality, of course, these lists are purely abstract. For us, though, we can
fill them with whatever we want.

[Wolfram
Alpha](http://www.wolframalpha.com/examples/pro-features/step-by-step-solutions/v)
will let you perform various manipulations on equations and expressions, even
with abstract variables. What's most useful about the manipulations is that it
will also provide "step-by-step solutions" of the transformations.

We can do the same here, with a custom setoid:

```agda
infix 4 _≡⋯≡_
infixr 5 _≡⟨_⟩_
data _≡⋯≡_ : A → A → Set a where
  [refl] : ∀ {x} →  x ≡⋯≡ x
  _≡⟨_⟩_ : ∀ {x} y {z} → String → y ≡⋯≡ z → x ≡⋯≡ z
  cong₁ : ∀ {x y z} {f : A → A}
        → String
        → x ≡⋯≡ y
        → f y ≡⋯≡ z
        → f x ≡⋯≡ z
  cong₂ : ∀ {x₁ x₂ y₁ y₂ z} {f : A → A → A}
        → String
        → x₁ ≡⋯≡ x₂
        → y₁ ≡⋯≡ y₂
        → f x₂ y₂ ≡⋯≡ z
        → f x₁ y₁ ≡⋯≡ z
```

## Isomorphism

The other loosish notion of equivalence is *isomorphism*
[@coquand_isomorphism_2013].

# Correct by construction

The Coq style is too write the implementation is correctness by construction
[@geuvers_automatically_2017].

```agda
infixr 0 ⟦⟧⇐_ ⟦_∷_⟨_⟩⟧⇐_
data Poly (expr : Carrier) : Set (a ⊔ ℓ) where
  ⟦⟧⇐_  : expr ≋ 0# → Poly expr
  ⟦_∷_⟨_⟩⟧⇐_ : ∀ x xs → Poly xs → expr ≋ (λ ρ → x Coeff.+ ρ Coeff.* xs ρ) → Poly expr

_⊞_ : ∀ {x y} → Poly x → Poly y → Poly (x + y)
(⟦⟧⇐ xp) ⊞ (⟦⟧⇐ yp) = ⟦⟧⇐ xp ⟨ +-cong ⟩ yp ⟨ trans ⟩ +-identityˡ _
(⟦⟧⇐ xp) ⊞ (⟦ y ∷ ys ⟨ ys′ ⟩⟧⇐ yp) = ⟦ y ∷ ys ⟨ ys′ ⟩⟧⇐ xp ⟨ +-cong ⟩ yp ⟨ trans ⟩ +-identityˡ _
(⟦ x ∷ xs ⟨ xs′ ⟩⟧⇐ xp) ⊞ (⟦⟧⇐ yp) = ⟦ x ∷ xs ⟨ xs′ ⟩⟧⇐ xp ⟨ +-cong ⟩ yp ⟨ trans ⟩ +-identityʳ _
(⟦ x ∷ xs ⟨ xs′ ⟩⟧⇐ xp) ⊞ (⟦ y ∷ ys ⟨ ys′ ⟩⟧⇐ yp) = ⟦ x Coeff.+ y ∷ xs + ys ⟨ xs′ ⊞ ys′ ⟩⟧⇐
  xp ⟨ +-cong ⟩ yp ⟨ trans ⟩  λ ρ → +-distrib _ _ _ _ ρ
```

# Other structures

Semiring has a free equivalent: [@rivas_monoids_2015]
