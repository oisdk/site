---
title: A Small Trick for Decidable Equality in Agda
tags: Agda
---

One of the types I have found extremely useful in Agda recently is `T`:

```agda
T : Bool → Type₀
T true  = ⊤
T false = ⊥
```

This type basically turns a Boolean into its "proof" counterpart.
It's useful because it means we can define predicates quite naturally as Boolean
functions, which we the upgrade using the `T` function.
To define `≤` on the natural numbers, for instance, in the past I might have written:

```agda
data _≤_ : ℕ → ℕ → Type₀ where
  z≤n : zero ≤ n
  s≤s : n ≤ m → suc n ≤ suc m
```

The problem with this type is that it has to be proven to be decidable
separately, and it doesn't actually carry any information that isn't already
given by the two indices.
So instead we could define a boolean function:

```agda
_≤ᴮ_ : ℕ → ℕ → Bool
zero  ≤ᴮ m     = true
suc n ≤ᴮ zero  = false
suc n ≤ᴮ suc m = n ≤ᴮ m
```

And define the relation in terms of that:

```agda
_≤_ : ℕ → ℕ → Type₀
n ≤ m = T (n ≤ᴮ m)
```

This type is:

#. Automatically decidable.
#. Automatically a proposition.
#. Automatically convertible (without constructors) along any of the equations
in its definition.

I won't go much more into depth on why these are really useful for cutting down
code length in Agda, but in this post I'm going to show a nice way to write
decidable equality instances without much trouble.

Writing instances for decidable equality in Agda can be annoying.
Here's a type for the ternary numbers:

```agda
infixl 5 _,0 _,1 _,2
data Tri : Type₀ where
  0t : Tri
  _,0 _,1 _,2 : Tri → Tri
```

And here's how we'd prove that they have decidable equality:

```agda
mod3 : Tri → Tri
mod3 0t = 0t
mod3 (x ,0) = x
mod3 (x ,1) = x
mod3 (x ,2) = x

infix 4 _≟_
_≟_ : (x y : Tri) → Dec (x ≡ y)
0t   ≟ 0t   = yes refl
0t   ≟ y ,0 = no λ ()
0t   ≟ y ,1 = no λ ()
0t   ≟ y ,2 = no λ ()
x ,0 ≟ 0t   = no λ ()
x ,0 ≟ y ,0 = ⟦yes cong _,0 ,no cong mod3 ⟧ (x ≟ y)
x ,0 ≟ y ,1 = no λ ()
x ,0 ≟ y ,2 = no λ ()
x ,1 ≟ 0t   = no λ ()
x ,1 ≟ y ,0 = no λ ()
x ,1 ≟ y ,1 = ⟦yes cong _,1 ,no cong mod3 ⟧ (x ≟ y)
x ,1 ≟ y ,2 = no λ ()
x ,2 ≟ 0t   = no λ ()
x ,2 ≟ y ,0 = no λ ()
x ,2 ≟ y ,1 = no λ ()
x ,2 ≟ y ,2 = ⟦yes cong _,2 ,no cong mod3 ⟧ (x ≟ y)
```

Even with some helper functions, this is 16 lines long ($O(n^2)$ the number of
constructors).
And in cubical Agda it's even more complex (since we can't pattern-match on
paths, the `no` cases get quite ugly).

So let's take another look at it, first defining the boolean equality function:

```agda
infix 4 _≡ᴮ_
_≡ᴮ_ : Tri → Tri → Bool
0t   ≡ᴮ 0t   = true
x ,0 ≡ᴮ y ,0 = x ≡ᴮ y
x ,1 ≡ᴮ y ,1 = x ≡ᴮ y
x ,2 ≡ᴮ y ,2 = x ≡ᴮ y
_    ≡ᴮ _    = false
```

Here the function is linear in the number of constructors of the type.
To turn this into a function for decidable equality, we will use the following
helper:

```agda
from-bool-eq :
  (_≡ᴮ_ : A → A → Bool) →
  (sound : ∀ x y → T (x ≡ᴮ y) → x ≡ y) →
  (complete : ∀ x → T (x ≡ᴮ x)) →
  (x y : A) → Dec (x ≡ y)
```

We'll take a look at this function's implementation in a second, but first let's
quickly use it to write a decidable equality instance for the `Tri` type:

```agda
sound : ∀ x y → T (x ≡ᴮ y) → x ≡ y
sound 0t     0t     p = refl
sound (x ,0) (y ,0) p = cong _,0 (sound x y p)
sound (x ,1) (y ,1) p = cong _,1 (sound x y p)
sound (x ,2) (y ,2) p = cong _,2 (sound x y p)

complete : ∀ x → T (x ≡ᴮ x)
complete 0t = tt
complete (x ,0) = complete x
complete (x ,1) = complete x
complete (x ,2) = complete x

_≟_ : (x y : Tri) → Dec (x ≡ y)
_≟_ = from-bool-eq _≡ᴮ_ sound complete
```

In terms of reducing boilerplate, this method means that we have to
pattern-match on $O(n)$ cases, rather than $O(n^2)$.
Also the `sound` and `complete` functions were extremely easy to write, much
easier than writing a decidable equality instance in Cubical Agda.

So, on to the `from-bool-eq` function: this function isn't extremely complex,
but it does use the odd definition of `Dec` which is now in Agda's standard
library.
This new `Dec` is basically a pair where the first component is a `Bool`
indicating whether the decision is yes or no; this means that often we get
faster computation if we only look at this first component.
It also means it reduces better in typechecking: see the [implementation in the
Agda standard
library](https://github.com/agda/agda-stdlib/blob/master/README/Design/Decidability.agda)
for more explanation.

```agda
record Dec {a} (A : Type a) : Type a where
  constructor _because_
  field
    does  : Bool
    why   : if does then A else ¬ A

pattern yes p  = true   because p
pattern no ¬p  = false  because ¬p
```

This odd implementation also means that this version of decidable equality
should be a little faster than the naive implementation.

The implementation is here:

```agda
from-bool-eq :
  (_≡ᴮ_ : A → A → Bool) →
  (sound : ∀ x y → T (x ≡ᴮ y) → x ≡ y) →
  (complete : ∀ x → T (x ≡ᴮ x)) →
  (x y : A) → Dec (x ≡ y)
from-bool-eq _≡ᴮ_ sound complete x y =
  map-dec
    (sound x y)
    (λ p → subst (λ z → T (x ≡ᴮ z)) p (complete x))
    (T? (x ≡ᴮ y))
```

With the following helper functions:

```agda
map-dec : (A → B) → (B → A) → Dec A → Dec B
map-dec to fro dec .does = dec .does
map-dec to fro (yes p) .why = to p
map-dec to fro (no ¬p) .why p = ¬p (fro p)

T? : ∀ x → Dec (T x)
T? x .does = x
T? false .why ()
T? true .why = tt
```

Anyway, I though this was a nice technique and a handy helper function.
It also means the fast definition of equality on nats is pretty straightforward:

```agda
sound-== : ∀ n m →  T (n ≡ᴮ m) → n ≡ m
sound-== zero zero p = refl
sound-== (suc n) (suc m) p = cong suc (sound-== n m p)

complete-== : ∀ n → T (n ≡ᴮ n)
complete-== zero = tt
complete-== (suc n) = complete-== n

discreteℕ : Discrete ℕ
discreteℕ = from-bool-eq _≡ᴮ_ sound-== complete-==
```
