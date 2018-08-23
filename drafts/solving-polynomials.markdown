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

It's the discrete convolution of the two lists.
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

Now these things have numerous uses, but what I've been using them for is their
"freeness". I'm going to be a bit fast and loose with the definitions here, but
bear with me: free objects are "minimal" examples of some class (class can
indeed be a Haskell class here, but it's more general). The classic example is
lists:

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

And you get *nothing else*. Combining lists isn't commutative, for instance.

The other thing we'll need is `foldMap`{.haskell}:

```haskell
foldMap :: forall m. Monoid m => (a -> m) -> List a -> m
```

`foldMap`{.haskell} kind of "interprets" the list in some underlying monoid.
Think about it like this: in the middle of writing some program, you find
yourself scrawling some massive, complex expression using the monoid
operations. However, indecisive programmer that you are, you can't quite decide
on *which* monoid you're going to end up using. Here's where lists come in: you
can procrastinate, writing all of your expressions in terms of lists, and then
interpreting them with `foldMap` when you're good and ready. In case you're
worried about the correctness of this approach, `foldMap` forms a valid monoid
homomorphism, which means it satisfies the laws:

```haskell
foldMap f (xs ++ ys) == foldMap f xs <> foldMap f ys
foldMap f empty == mempty
```

In other words, it doesn't make a difference if you use the monoid operations on
lists and then `foldMap`, or if you `foldMap` and then use the monoid operations
on the result: you'll still get the same answer.

The somewhat silly example above probably didn't convince you of the usefulness
of the homomorphism. After all, when you decide what monoid you're going to use,
why not just go back to the original expressions and sub it in?

Well, there's one place you really *do* have to postpone choosing concrete
values: inside a lambda. Now, ordinarily, this would be no problem, since most
of the time we only inspect lambdas by running them. This is not the case if we
want too *prove* things about those lambdas, though. Consider the proposition:

```agda
∀ w x y z → (w <> x) <> (y <> z) ≡ w <> ((x <> y) <> z)
```

We know it's true, because `<>` is associative, so parentheses don't matter, but
it's difficult to convince the compiler of that fact. If there were concrete
values subbed in, we could run the expression, and just look at the result:
again, though, we want to prove this property in the abstract. If we use
*lists*, though:

```agda
prop : ∀ {a} {A : Set a} {w x y z : A}
     → ([ w ] ++ [ x ]) ++ ([ y ] ++ [ z ])
     ≡ [ w ] ++ (([ x ] ++ [ y ]) ++ [ z ])
prop = refl
```

The expression doesn't rely on the contents of the lists, so it can be run
without inspecting them. What's more, because we know that `foldMap`{.haskell}
forms a homomorphism, we can use the above proof to prove the original identity.
Effectively, lists are a normal form for expressions over monoids: if the two
normalized expressions are equal, then the expressions themselves must be equal.
The implementation is a little weird, but once done you can write stuff like
this:

```agda
prop : ∀ w x y z → (w ∙ x) ∙ (y ∙ z) ≈ w ∙ ((x ∙ y) ∙ z)
prop = solve 4
  (λ w x y z → (w ⊕ x) ⊕ (y ⊕ z) ⊜ w ⊕ ((x ⊕ y) ⊕ z))
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

Our first stab at a representation will look like this:

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

Here, we've defined addition and multiplication. One of the important concepts
we'll rely on is *Horner's rule*: it's a method for evaluating these polynomials
that reduces the number of multiplications we have to perform. It looks like
this:

```agda
⟦_⟧ : Poly → Carrier → Carrier
⟦ p ⟧ ρ = List.foldr (λ x xs → x + xs * ρ) 0# p
```

# Multiple Variables

...

(naive version)

# Proving Homomorphism

Writing more involved proofs in Agda is actually reasonably pleasant. For
instance, later on we'll be using this definition of exponentiation:

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
pow-add x zero j = *-identityˡ (x ^ j)
pow-add x (suc i) j =
  begin
    x ^ suc i * x ^ j
  ≡⟨⟩
    (x * x ^ i) * x ^ j
  ≈⟨ *-assoc x _ _ ⟩
    x * (x ^ i * x ^ j)
  ≈⟨ *≫ pow-add x i j ⟩
    x * x ^ (i ℕ.+ j)
  ≡⟨⟩
    x ^ suc (i ℕ.+ j)
  ∎
```

First, the type of the proof uses $\approx$ rather than the normal $\equiv$.
That's because we're not actually using propositional equality. We're using an
arbitrary equivalence relation supplied along with the ring. We'll see later how
to use this flexibility to do some cool things.

Next, the function is defined as two clauses: we recurse on `i`, as you might
expect in an Idris-style proof.

The second clause, though, is a total departure from the normal syntax. There's
nothing built-in about it, though: it's all normal operators and functions
defined in the standard library. In the brackets (`⟨ ⟩`) is the reason for the
equality on either side.

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

$$ P \ast X^i + c $$

This didn't make a huge amount of sense to me, though. Since we're representing
the preceding gap, I decided to go with the following translation:

$$ (P \ast X + c) * X^i $$

By way of example, the polynomial:

$$ 3 + 2x² + 4x⁵ + 2x⁷ $$

Will be represented as:

```agda
[(3,0),(2,1),(4,2),(2,1)]
```

Or, mathematically:

$$ x^0 * (3 + x * x^1 * (2 + x * x^2 * (4 + x * x^1 * (2 + x * 0)))) $$


Also, we can kill two birds with one stone here: if we disallow zeroes
*entirely* in the list, we lose the gaps, and we also get a unique
representation. Finally, we have a representation:

```agda
mutual
  Poly : ℕ → Set (a ⊔ ℓ)
  Poly zero = Lift ℓ Carrier
  Poly (suc n) = Coeffs n

  Coeffs : ℕ → Set (a ⊔ ℓ)
  Coeffs n = List (Coeff n × ℕ)

  infixr 4 0≠_
  record Coeff (i : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor 0≠_
    field
      poly : Poly i
      .{poly≠0} : ¬ Zero i poly

  Zero : ∀ n → Poly n → Set ℓ
  Zero zero (lift x) = Zero-C x
  Zero (suc n) [] = Lift ℓ ⊤
  Zero (suc n) (x ∷ xs) = Lift ℓ ⊥
```

The coefficients are ensured to be nonzero, as promised. We define a function
(`Zero`) which returns a set based on a polynomial: the record `Coeff` stores an
element of that set in its second field. When the polynomial is zero, though:
the set returned is the empty set ($\bot$): so there's no way that there's
actually an element in that second field. I've also marked the proof as
irrelevant (that's the dot before it), so that it's not computed at runtime.

To make things easier, we can define a normalizing variant of `∷`:

```agda
zero? : ∀ {n} → (p : Poly n) → Dec (Zero n p)
zero? {zero} (lift x) = x ≟C 0#
zero? {suc n} [] = yes (lift tt)
zero? {suc n} (x ∷ xs) = no lower

infixr 8 _⍓_
_⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
[] ⍓ i = []
((x , j) ∷ xs) ⍓ i = (x , j ℕ.+ i) ∷ xs

infixr 5 _∷↓_
_∷↓_ : ∀ {n} → (Poly n × ℕ) → Coeffs n → Coeffs n
(x , i) ∷↓ xs with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = (x ,~ ¬p , i) ∷ xs
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

While the gapless representation is *meant* to be more efficient, it looks unary
to me.

...

# Termination & Redundancy

Totality and nontermination isn't actually a problem I've encountered much in
Agda, but it does occasionally come up. Even when it does, the complaints often
(not always, but often) point towards redundancy, rather than necessary
complexity. For instance, the straightforward translation of `⊞` doesn't pass:

```agda
_⊞_ : ∀ {n} → Poly n → Poly n → Poly n
_⊞_ {zero} (lift x) (lift y) = lift (x + y)
_⊞_ {suc n} [] ys = ys
_⊞_ {suc n} (x ∷ xs) [] = x ∷ xs
_⊞_ {suc n} ((x , i) ∷ xs) ((y , j) ∷ ys) with ℕ.compare i j
... | ℕ.less    .i k = (x , i) ∷ xs ⊞ ((y , k) ∷ ys)
... | ℕ.equal   .i   = (poly x ⊞ poly y , i) ∷↓ (xs ⊞ ys)
... | ℕ.greater .j k = (y , j) ∷ ((x , k) ∷ xs) ⊞ ys
```

# List Homomorphism
@mu_algebra_2009

# Other structures

Semiring has a free equivalent: [@rivas_monoids_2015]

# Correct by construction

@geuvers_automatically_2017

@mcbride_polynomial_2018

# K

# Setoid

traced
