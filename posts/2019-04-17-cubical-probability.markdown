---
title: Cubical Agda and Probability Monads
tags: Agda, Probability
---

[Cubical Agda](https://agda.readthedocs.io/en/latest/language/cubical.html) has
just come out, and I've been playing around with it for a bit.
There's a bunch of info out there on the theory of cubical types, and Homotopy
Type Theory more generally (cubical type theory is kind of like an
"implementation" of Homotopy type theory), but I wanted to make a post
demonstrating cubical Agda in practice, and one of its cool uses from a
programming perspective.

# So What is Cubical Agda?

I don't really know!
Cubical type theory is quite complex (even for a type theory), and I'm not
nearly qualified to properly explain it.
In lieu of a proper first-principles explanation, then, I'll try and give a
few examples of how it differs from normal Agda, before moving on to the main
example of this post.

Extensionality

:   One of the big annoyances in standard Agda is that we can't prove the
    following:
    ```agda
    extensionality : ∀ {f g : A → B}
                  → (∀ {x} → f x ≡ g x)
                  → f ≡ g
    ```
    It's emblematic of a wider problem in Agda: we can't say "two things are
    equal if they always behave the same".
    Infinite types, for instance (like streams) are often only equal via
    bisimulation: we can't translate this into normal equality in standard Agda.
    Cubical type theory, though, has a different notion of "equality", which
    allow a wide variety of things (including bisimulations and extensional
    proofs) to be translated into a proper equality

Isomorphisms

:   One of these such things we can promote to a "proper equality" is an
    isomorphism.
    In the [cubical repo](https://github.com/agda/cubical) this is used to [prove
    things about binary
    numbers](https://github.com/agda/cubical/blob/8391a4835b3d2478e9394c6c3ec7e6fff42ede62/Cubical/Data/BinNat/BinNat.agda):
    by proving that there's an isomorphism between the Peano numbers and binary
    numbers, they can lift any properties on the Peano numbers to the binary
    numbers.

So those are two useful examples, but the *most* interesting use I've seen so
far is the following:

# Higher Inductive Types

Higher Inductive Types are an extension of normal inductive types, like the
list:
```agda
data List {a} (A : Set a) : Set a where
  [] : List A
  _∷_ : A → List A → List A
```

They allow us to add new equations to a type, as well as constructors.
To demonstrate what this means, as well as why you'd want it, I'm going to talk
about free objects.

Very informally, a free object on some algebra is the *minimal* type which
satisfies the laws of the algebra.
Lists, for instance, are the free monoid.
They satisfy all of the monoid laws ($\bullet$ is `++` and $\epsilon$ is `[]`):

$$(x \bullet y) \bullet z = x \bullet (y \bullet z)$$
$$x \bullet \epsilon = x$$
$$\epsilon \bullet x = x$$

But *nothing else*.
That means they don't satisfy any extra laws (like, for example, commutativity),
and they don't have any extra structure they don't need.

How did we get to the definition of lists from the monoid laws, though?
It doesn't look anything like them.
It would be nice if there was some systematic way to construct the corresponding
free object given the laws of an algebra.
Unfortunately, in normal Agda, this isn't possible.
Consider, for instance, if we added the commutativity law to the algebra:
$$x \bullet y = y \bullet x$$
Not only is it not obvious how we'd write the corresponding free object, it's
actually *not possible* in normal Agda!

This kind of problem comes up a lot: we have a type, and we want it to obey just
*one more* equation, but there is no inductive type which does so.
Higher Inductive Types solve the problem in quite a straightforward way.
So we want lists to satisfy another equation?
Well, just add it to the definition!

```agda
data List {a} (A : Set a) : Set a where
  [] : List A
  _∷_ : A → List A → List A
  comm : ∀ xs ys → xs ++ ys ≡ ys ++ xs
```

Now, when we write a function that processes lists, Agda will check that the
function behaves the same on `xs ++ ys` and `ys ++ xs`.
As an example, here's how you might define the free monoid as a HIT:
```agda
data FreeMonoid {a} (A : Set a) : Set a where
  [_] : A → FreeMonoid A
  _∙_ : FreeMonoid A → FreeMonoid A → FreeMonoid A
  ε : FreeMonoid A
  ∙ε : ∀ x → x ∙ ε ≡ x
  ε∙ : ∀ x → ε ∙ x ≡ x
  assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
```
It's quite a satisfying definition, and very easy to see how we got to it from
the monoid laws.

Now, when we write functions, we have to prove that those functions themselves
also obey the monoid laws.
For instance, here's how we would take the length:
```agda
length : FreeMonoid A → ℕ
length [ x ] = 1
length (xs ∙ ys) = length xs + length ys
length ε = 0
length (∙ε xs i) = +-identityʳ (length xs) i
length (ε∙ xs i) = +-identityˡ (length xs) i
length (assoc xs ys zs i) = +-assoc (length xs) (length ys) (length zs) i
```

The first three clauses are the actual function: they deal with the three
normal constructors of the type.
The next three clauses prove that those previous clauses obey the equalities
defined on the type.

With the preliminary stuff out of the way, let's get on to the type I wanted to
talk about:

# Probability

First things first, let's remember the classic definition of the probability
monad:

```haskell
newtype Prob a = Prob { runProb :: [(a, Rational)] }
```

Definitionally speaking, this doesn't really represent what we're talking about.
For instance, the following two things express the same distribution, but have
different representations:

```haskell
Prob [(True, 1 / 4), (True, 1 / 4), (False, 1 / 2)]
Prob [(True , 1 / 2), (False, 1 / 2)]
```

So it's the perfect candidate for an extra equality clause like we had above.

Second, in an effort to generalise, we won't deal specifically with `Rational`,
and instead we'll use any semiring.
After all of that, we get the following definition:

```agda
infixr 5 _&_∷_
data 𝒫 (A : Set a) : Set (a ⊔ s) where
  []  : 𝒫 A
  _&_∷_ : (p : Carrier) → (x : A) → 𝒫 A → 𝒫 A
  dup : ∀ p q x xs → p & x ∷ q & x ∷ xs ≡ p + q & x ∷ xs
  com : ∀ p x q y xs → p & x ∷ q & y ∷ xs ≡ q & y ∷ p & x ∷ xs
  del : ∀ x xs → 0# & x ∷ xs ≡ xs
```

The three extra conditions are pretty sensible: the first removes duplicates,
the second makes things commutative, and the third removes impossible events.

Let's get to writing some functions, then:

```agda
sample : (A → Carrier) → 𝒫 A → Carrier
sample f [] = 0#
sample f (p & x ∷ xs) = p * f x + sample f xs
sample f (dup p q x xs i) = begin[ i ]
  p * f x + (q * f x + sample f xs) ≡˘⟨ +-assoc (p * f x) (q * f x) (sample f xs) ⟩
  (p * f x + q * f x) + sample f xs ≡˘⟨ cong (_+ sample f xs) (⟨+⟩* p q (f x))  ⟩
  (p + q) * f x + sample f xs ∎
sample f (swap p x q y xs i) = begin[ i ]
  p * f x + (q * f y + sample f xs) ≡˘⟨ +-assoc (p * f x) (q * f y) (sample f xs) ⟩
  p * f x + q * f y + sample f xs   ≡⟨ cong (_+ sample f xs) (+-comm (p * f x) (q * f y)) ⟩
  q * f y + p * f x + sample f xs   ≡⟨ +-assoc (q * f y) (p * f x) (sample f xs) ⟩
  q * f y + (p * f x + sample f xs) ∎
sample f (del x xs i) = begin[ i ]
  0# * f x + sample f xs ≡⟨ cong (_+ sample f xs) (0* (f x)) ⟩
  0# + sample f xs       ≡⟨ 0+ (sample f xs) ⟩
  sample f xs ∎
```

This is much more involved than the free monoid function, but the principle is
the same: we first write the actual function (on the first three lines), and
then we show that the function doesn't care about the "rewrite rules" we have in
the next three clauses.

Before going any further, we will have to amend the definition a little.
The problem is that if we tried to prove something about any function on our
`𝒫` type, we'd have to prove equalities *between equalities* as well.
I'm sure that this is possible, but it's very annoying, so I'm going to use a
technique I saw in [this repository](https://github.com/L-TChen/FiniteSets).
We add another rule to our type, stating that all equalities on the type are
themselves equal.
The clause itself looks like this:

```agda
trunc : isSet (𝒫 A)
```

# Eliminators

Unfortunately, after adding that case we have to deal with it explicitly in
every pattern-match on `𝒫`.
We can get around it by writing an eliminator for the type which deals with it
itself.
Eliminators are often irritating to work with, though: we give up the nice
pattern-matching syntax we get when we program directly.
It's a bit like having to rely on church encoding everywhere.

However, we can get back some pattern-like syntax if we use *copatterns*. Here's
an example of what I mean, for folds on lists:

```agda
record [_↦_] (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    [_][] : B
    [_]_∷_ : A → B → B
  [_]↓ : List A → B
  [ [] ]↓ = [_][]
  [ x ∷ xs ]↓ = [_]_∷_ x [ xs ]↓
open [_↦_]

sum-alg : [ ℕ ↦ ℕ ]
[ sum-alg ][] = 0
[ sum-alg ] x ∷ xs = x + xs

sum : List ℕ → ℕ
sum = [ sum-alg ]↓
```

For the probability monad, there's an eliminator for the whole thing, and
eliminator for propositional proofs, and a normal eliminator for folding.
Here's one in action, to define `map`:

```agda
map : (A → B) → [ A ↦ 𝒫 B ]
[ map f ] p & x ∷ xs = p & f x ∷ xs
[ map f ][] = []
[ map f ]-set = trunc
[ map f ]-dup p q x xs = dup p q (f x) xs
[ map f ]-com p x q y xs = com p (f x) q (f y) xs
[ map f ]-del x xs = del (f x) xs
```

And here's one proving that union is associative:

```agda
∪-assoc : ∀ ys zs → ⟦ xs ∈𝒫 A ⇒ xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs ⟧
⟦ ∪-assoc ys zs ⟧-prop = trunc _ _
⟦ ∪-assoc ys zs ⟧[] = refl
⟦ ∪-assoc ys zs ⟧ p & x ∷ xs ⟨ P ⟩ = cong (p & x ∷_) P
```

Finally, the main event: monadic bind.

```agda
_=<< : (A → 𝒫 B) → [ A ↦ 𝒫 B ]
[ f =<< ] p & x ∷ xs = [ cond p ]↓ (f x) ∪ xs
[ f =<< ][] = []
[ f =<< ]-set = trunc
[ f =<< ]-del x xs = cong (_∪ xs) (⟦ cond-0 ⟧⇓ (f x))
[ f =<< ]-dup p q x xs =
  [ cond p ]↓ (f x) ∪ [ cond q ]↓ (f x) ∪ xs   ≡⟨ ⟦ ∪-assoc ([ cond q ]↓ (f x)) xs ⟧⇓ ([ cond p ]↓ (f x))⟩
  ([ cond p ]↓ (f x) ∪ [ cond q ]↓ (f x)) ∪ xs ≡⟨ cong (_∪ xs) (⟦ cond-distrib p q ⟧⇓ (f x) ) ⟩
  [ cond (p + q) ]↓ (f x) ∪ xs ∎
[ f =<< ]-com p x q y xs =
  [ cond p ]↓ (f x) ∪ [ cond q ]↓ (f y) ∪ xs   ≡⟨ ⟦ ∪-assoc ([ cond q ]↓ (f y)) xs ⟧⇓ ([ cond p ]↓ (f x)) ⟩
  ([ cond p ]↓ (f x) ∪ [ cond q ]↓ (f y)) ∪ xs ≡⟨ cong (_∪ xs) (⟦ ∪-comm ([ cond q ]↓ (f y)) ⟧⇓ ([ cond p ]↓ (f x))) ⟩
  ([ cond q ]↓ (f y) ∪ [ cond p ]↓ (f x)) ∪ xs ≡˘⟨ ⟦ ∪-assoc ([ cond p ]↓ (f x)) xs ⟧⇓ ([ cond q ]↓ (f y)) ⟩
  [ cond q ]↓ (f y) ∪ [ cond p ]↓ (f x) ∪ xs ∎

_>>=_ : 𝒫 A → (A → 𝒫 B) → 𝒫 B
xs >>= f = [ f =<< ]↓ xs
```

# Conclusion

I've really enjoyed working with cubical Agda so far, and the proofs above were
a pleasure to write.
I think I can use the above definition to get a workable differential privacy
monad, also.

Anyway, all the code is available
[here](https://oisdk.github.io/agda-cubical-probability/Probability.html).
