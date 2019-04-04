---
title: The p-Adic Numbers in Agda
tags: Agda
bibliography: p-Adics.bib
header-includes:
  - \usepackage{mathtools}
  - \usepackage{mnsymbol}
  - \usepackage{fdsymbol}
---

# Introduction

Recently I happened across the [$p$-adic
numbers](https://ncatlab.org/nlab/show/p-adic+number) in the context of trying
to formally verify something for work. They caught my eye, so I thought I'd go
through some of their interesting properties here. Also, I have dived into
[Agda](https://agda.readthedocs.io/en/latest/) recently, and I felt I should
start writing something on it. As I'm still just starting out, criticism of the
code is very welcome.

# Positional Number Systems

If you've ever tried to implement a positional number system in a language like
Agda, you'll probably notice two problems with the naïve approach:

Order

:   If you represent the numbers as they're written (i.e.,
    most-significant-digit first), binary operations are a pain. Take, for
    instance, the numbers "102" and "35". The first digits of each are actually
    in different units: hundreds and tens, respectively. So you represent them
    in reverse, starting with the ones and increasing from there:

    ```agda
    Decimal : Set
    Decimal = List (Fin 10)

    102₁₀ : Decimal
    102₁₀ = 2 ∷ 0 ∷ 1 ∷ []

    35₁₀ : Decimal
    35₁₀ = 5 ∷ 3 ∷ []
    ```

Redundancy

:   Once you've fixed the order, you run into another problem: trailing zeroes.
    Because we haven't enforced any rules about trailing zeroes, every number
    has an infinite number of representations. 35 above, for instance:
    
    ```agda
    5 ∷ 3 ∷ []
    5 ∷ 3 ∷ 0 ∷ []
    5 ∷ 3 ∷ 0 ∷ 0 ∷ []
    ```
    
    By all rights, these three numbers *should* be the same.
    
    One way of solving the problem is by embracing it: we say that every number
    comes with infinite trailing zeroes. So now there's only *one* way to
    represent 35:
    
    ```agda
    5 ∷ 3 ∷ 0 ...
    ```
    
    Or, written down: 0̅35. That bar is for "repeating", by the way, and it's
    called a [vinculum](https://en.wikipedia.org/wiki/Vinculum_(symbol)).

# The p-Adic Numbers

Both of these adaptations actually give you a number system similar to that of
the $p$-adics. Informally, the $p$-adic numbers are numbers written down in base
$p$, where the trailing digits (if there are any), go to the *left*, not the
right. A little more rigorously, the $p$-adics are a completion[^prime] of the
rational numbers: i.e. they add the reals to the rational numbers, while
maintaining a proper, law-abiding metric (a metric can be thought of as a
distance measure).

[^prime]: Note that the $p$-adics are a completion only for a prime $p$.

Back to the positional view of things, the particular metric that the $p$-adics
use is a little strange: it views digits to the *right* as much more important
than digits to the left. This means that, for instance, $301_{10}$ is "closer"
to $2_{10}$ than it is to $305_{10}$. It also implies a different ordering:
one that's lexicographical from the right.

This stuff should be sounding suspiciously like the natural changes we made
above to make positional numbers more comfortable for use in computation.
Indeed, compare the ordering we'd need for positional numbers (ordered
least-significant-digit first):

```haskell
newtype Positional
    = Positional
    { runPositional :: [Integer]
    } deriving Eq
    
instance Ord Positional where
    compare = go EQ `on` runPositional
      where
        go a (x:xs) (y:ys) = go (compare x y <> a) xs ys
        go _ [] (_:_) = LT
        go _ (_:_) [] = GT
        go a [] [] = a
```

To the natural one for $p$-adics, where we just use the built-in lexicographical
ordering:

```haskell
newtype Positional
    = Positional
    { runPositional :: [Integer]
    } deriving (Eq, Ord)
```

There's one extra benefit: *negative* numbers.

\begin{equation}
  \minus1_{10} = \overbar{9}_{10}
\end{equation}

This looks a lot like the wraparound in two's complement arithmetic, but it
works out just fine in the $p$-adics, again with *no redundancy*.

As it turns out, using $p$-adics to represent numbers on computers has already
been explored [@hehner_new_1979]: using them as a basis in Agda, though, I
haven't seen before [other than @pelayo_univalent_2015, which to be totally
honest I don't understand].

# Implementation: Digits

The first thing we'll need is a way to describe each digit. Instead of using the
usual `Fin`{.haskell}-based approach, I'm going to role my own type, which
represents a unit interval on the number line:

```agda
data S⟨_+_⟩≡_ : ℕ → ℕ → ℕ → Set where
  ⊢  : ∀ {x} → S⟨ 0 + x ⟩≡ suc x
  _⊸ : ∀ {x y z}
        → S⟨ x + suc y ⟩≡ z
        → S⟨ suc x + y ⟩≡ z
```

It's an inductive data type, with a base case being the left-hand-side of the
interval, and the step (⊸) moving the interval one place to the right. It's
phrased as a proof that the space below and above the interval are related to
the size of the interval ($p$) like so:

\begin{equation}
  1 + \textit{below} + \textit{above} = p
\end{equation}

In fact, we can make that correspondence explicit:

```agda
S⟨+⟩≡⇒S+≡ : ∀ {x′ y′ n}
          → (x : S⟨ x′ + y′ ⟩≡ n)
          → suc (x′ + y′) ≡ n
S⟨+⟩≡⇒S+≡ ⊢ = refl
S⟨+⟩≡⇒S+≡ {x′} {y′} (x ⊸)
  rewrite sym (Prop.+-suc x′ y′) =
  S⟨+⟩≡⇒S+≡ x
```

The reason I'm using this more complex representation (rather than `Fin`{.agda})
is that it is easier to reason about things like *overflow*: we store, in this
representation, both the value of the digit itself and the amount of space left
before overflow. This makes the operation to check for overflow a comparison of
two of the indices:

```agda
inbounds₊ : ∀ {x₁ y₁ x₂ y₂ n}
          → S⟨ x₁ + y₁ ⟩≡ n
          → S⟨ x₂ + y₂ ⟩≡ n
          → Dec (x₁ ≤ y₂)
inbounds₊ = go id id
  where
  go : ∀ {A x₁ y₁ x₂ y₂ n}
     → (x₁ ≤ y₂ →   A)
     → (x₁ ≰ y₂ → ¬ A)
     → S⟨ x₁ + y₁ ⟩≡ n
     → S⟨ x₂ + y₂ ⟩≡ n
     → Dec A
  go               yes′ no′ ⊢     y = yes (yes′ ℕ.z≤n)
  go {y₂ = zero}   yes′ no′ (x ⊸) y = no  (no′ λ ())
  go {y₂ = suc y₂} yes′ no′ (x ⊸) y =
    go (yes′ ∘ ℕ.s≤s)
       (λ x₁≰y₂ → no′ (x₁≰y₂ ∘ ℕ.≤-pred))
       x (y ⊸)
```

The "sum" channel then, for the adder, looks like this:

```agda
sumˡ : (x₁ x₂ y₂ : ℕ) → ℕ
sumˡ zero     x₂ y₂       = x₂
sumˡ (suc x₁) x₂ (suc y₂) = sumˡ x₁ (suc x₂) y₂
sumˡ (suc x₁) x₂ zero     = x₁

sumʳ : (x₁ y₁ y₂ : ℕ) → ℕ
sumʳ zero     y₁ y₂       = y₂
sumʳ (suc x₁) y₁ (suc y₂) = sumʳ x₁ (suc y₁) y₂
sumʳ (suc x₁) y₁ zero     = suc y₁

sum₊  : ∀ {x₁ y₁ x₂ y₂ n}
      → S⟨ x₁ + y₁ ⟩≡ n
      → S⟨ x₂ + y₂ ⟩≡ n
      → S⟨ sumˡ x₁ x₂ y₂ + sumʳ x₁ y₁ y₂ ⟩≡ n
sum₊               ⊢     y = y
sum₊ {y₂ = suc y₂} (x ⊸) y = sum₊ x (y ⊸)
sum₊ {y₂ = zero}   (x ⊸) y = x
```

Finally, the full thing:

```agda
adder : ∀ {x₁ y₁ x₂ y₂ n}
      → S⟨ x₁ + y₁ ⟩≡ n
      → S⟨ x₂ + y₂ ⟩≡ n
      → Dec (x₁ ≤ y₂) × S⟨ sumˡ x₁ x₂ y₂ + sumʳ x₁ y₁ y₂ ⟩≡ n
adder = go id id
  where
  go : ∀ {A x₁ y₁ x₂ y₂ n}
     → (x₁ ≤ y₂ →   A)
     → (x₁ ≰ y₂ → ¬ A)
     → S⟨ x₁ + y₁ ⟩≡ n
     → S⟨ x₂ + y₂ ⟩≡ n
     → Dec A × S⟨ sumˡ x₁ x₂ y₂ + sumʳ x₁ y₁ y₂ ⟩≡ n
  go               y′ n′ ⊢     y = yes (y′ ℕ.z≤n)  , y
  go {y₂ = zero}   y′ n′ (x ⊸) y = no  (n′ (λ ())) , x
  go {y₂ = suc y₂} y′ n′ (x ⊸) y =
    go (y′ ∘ ℕ.s≤s)
       (λ x₁≰y₂ → n′ (x₁≰y₂ ∘ ℕ.≤-pred))
       x (y ⊸)
```

# Integers

For the positional system, we'll represent the $p$-adics (as promised) as an
infinite expansion of digits in base $p$. In Agda, infinite structures are
usually described using
[coinduction](http://agda.readthedocs.io/en/v2.5.4.1/language/coinduction.html).

Before that, though, we'll need a wrapper for our digits which hides the
indices: we'll call it a point on the line $\left[ 0 , n \right)$.

This is just a wrapper around the sliding proof which hides the above
and below types. The ``point'' we refer to is the lower bound of the
unit interval.
```agda
record Point (n : ℕ) : Set where
  constructor At
  field
    {below above} : ℕ
    point : S⟨ below + above ⟩≡ n
```

Finally, we can represent our $p$-adics. For coinductive types, a good way to
think about them is to try and describe an interface of fields which completely
describe the type (rather than a series of cases, as one would in an inductive
type). For the $p$-adics, that's going to be the least-significant-digit and the
rest, or, phrased a different way, the number "$\text{mod} \: p$" and the number
"$\text{div} \: p$":

```agda
record ℤ (p : ℕ) : Set where
  constructor _+p⟨_⟩
  coinductive
  field
    modₚ : Point p
    divₚ : ℤ p
```

The way you construct values of coinductive types is by using
[copatterns](http://agda.readthedocs.io/en/v2.5.4.1/language/copatterns.html):
you define each accessor. This makes termination (or prductivity, rather)
checking easier for infinite and coinductive types. Here, for instance, we
define 0:

```agda
0ₚ : ∀ {n} → ℤ (suc n)
modₚ 0ₚ = At ⊢
divₚ 0ₚ = 0ₚ
```

I quite like how this reads: 

\begin{gather}
  0 & \text{mod} & p = 0 \\
  0 & \text{div} & p = 0
\end{gather}

Anyway, it applies well to addition:

```agda
increment : ∀ {p} → ℤ p → ℤ p
modₚ (increment {suc _} x) with modₚ x
... | At {above = zero}  _ = At ⊢
... | At {above = suc _} y = At (y ⊸)
modₚ (increment {zero} x) = ⊥-elim (n≮0 (mod-w x))
divₚ (increment x) with above (modₚ x)
... | zero  = increment (divₚ x)
... | suc _ = divₚ x

infixl 6 _+_
_+_ : ∀ {p} → ℤ p → ℤ p → ℤ p
modₚ (x + y) = At (sum₊ (mod-w x) (mod-w y))
divₚ (x + y) with inbounds₊ (mod-w x) (mod-w y)
... | yes _ = divₚ x + divₚ y
... | no  _ = divₚ x + increment (divₚ y)
```
