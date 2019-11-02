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
{-# OPTIONS --cubical --safe #-}

open import Prelude

variable
  t : Level
  T : ℕ → Set t
  p : Level
  P : Set p
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
offer an alternative representation of ℕ that's tolerably efficient (well,
depending on who's doing the tolerating).
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

Right, now on to some actual binary numbers.
The obvious way (a list of bits) is insufficient, as it allows multiple
representations of the same number (because of the trailing zeroes).
Picking a more clever implementation is tricky, though.
One way splits it into two types:

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
I like to reuse types in combination with pattern synonyms (rather than defining
new types), as it can often make parallels between different functions clearer.

```agda
Bit : Set
Bit = Bool

pattern 1ᵇ = false
pattern 2ᵇ = true

𝔹 : Set
𝔹 = List Bit
```

<!--
```agda
variable
  d : Bit
  ds : 𝔹
```
-->

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
of the post (although it is very short, as a consequence of the simple
definitions).

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
𝔹→ℕ→𝔹 (1ᵇ ∷ xs) =           2*⇔1ᵇ∷ ⟦ xs ⇓⟧  ; cong (1ᵇ ∷_) (𝔹→ℕ→𝔹 xs)
𝔹→ℕ→𝔹 (2ᵇ ∷ xs) = cong inc (2*⇔1ᵇ∷ ⟦ xs ⇓⟧) ; cong (2ᵇ ∷_) (𝔹→ℕ→𝔹 xs)

inc⇔suc : ∀ n → ⟦ inc n ⇓⟧ ≡ suc ⟦ n ⇓⟧
inc⇔suc [] = refl
inc⇔suc (1ᵇ ∷ xs) = refl
inc⇔suc (2ᵇ ∷ xs) = cong (suc ∘ 2*) (inc⇔suc xs)

ℕ→𝔹→ℕ : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
ℕ→𝔹→ℕ zero    = refl
ℕ→𝔹→ℕ (suc n) = inc⇔suc ⟦ n ⇑⟧ ; cong suc (ℕ→𝔹→ℕ n)

𝔹⇔ℕ : 𝔹 ⇔ ℕ
𝔹⇔ℕ = iso ⟦_⇓⟧ ⟦_⇑⟧ ℕ→𝔹→ℕ 𝔹→ℕ→𝔹
```

</details>

# Binary Arrays

Now on to the data structure.
Here's its type.

```agda
infixr 5 _1∷_ _2∷_
data Array (T : ℕ → Type a) : 𝔹 → Type a where
  []  : Array T []
  _∷_ : T (bool 0 1 d) → Array (T ∘ suc) ds → Array T (d ∷ ds)

pattern _1∷_ x xs = _∷_ {d = 1ᵇ} x xs
pattern _2∷_ x xs = _∷_ {d = 2ᵇ} x xs
```

So it is a list-like structure, which contains elements of type `T`.
`T` is the type of trees in the array: making the array generic over the types
of trees is a slight departure from the norm.
Usually, we would just use a perfect tree or something:

```agda
module Prelim where
  Perfect : Set a → ℕ → Set a
  Perfect A zero = A
  Perfect A (suc n) = Perfect (A × A) n
```

By making the tree type a parameter, though, we actually *simplify* some of the
code for manipulating the tree.
It's basically the same trick as the type-changing parameter in `vec-foldl`.

As well as that, of course, we can use the array with more exotic tree types.
With binomial trees, for example, we get a binomial heap:

```agda
mutual
  data BinomNode (A : Set a) : ℕ → Set a where
    binom-leaf   : BinomNode A 0
    binom-branch : Binomial A n → BinomNode A n → BinomNode A (suc n)

  Binomial : Set a → ℕ → Set a
  Binomial A n = A × BinomNode A n
```

But we'll stick to the random-access lists for now.

# Top-down and Bottom-up Trees

The perfect trees above are actually a specific instance of a more general data
type: exponentiations of functors.

```agda
_^_ : (Set a → Set a) → ℕ → Set a → Set a
(F ^ zero ) A = A
(F ^ suc n) A = (F ^ n) (F A)

Nest : (Set a → Set a) → Set a → ℕ → Set a
Nest F A n = (F ^ n) A

Pair : Set a → Set a
Pair A = A × A

Perfect : Set a → ℕ → Set a
Perfect = Nest Pair
```

<!--

```agda
variable
  F : Set a → Set a
```

-->

It's a nested datatype, built in a bottom-up way.
This is in contrast to, say, the binomial trees above, which are top-down.

# Construction

Our first function on the array is `cons`, which inserts an element:

```agda
cons : (∀ n → T n → T n → T (suc n))
     → T 0 → Array T ds → Array T (inc ds)
cons branch x [] = x 1∷ []
cons branch x (y 1∷ ys) = branch 0 x y 2∷ ys
cons branch x (y 2∷ ys) = x 1∷ cons (branch ∘ suc) y ys
```

Since we're generic over the type of trees, we need to pass in the "branch"
constructor (or function) for whatever tree type we end up using.
Here's how we'd implement such a branch function for perfect trees.

```agda
perf-branch : ∀ n → Perfect A n → Perfect A n → Perfect A (suc n)
perf-branch zero = _,_
perf-branch (suc n) = perf-branch n
```

One issue here is that the `perf-branch` function probably doesn't optimise to
the correct complexity, because the `n` has to be scrutinised repeatedly.
The alternative is to define a `cons` for nested types, like so:

```agda
nest-cons : (∀ {A} → A → A → F A) → A → Array (Nest F A) ds → Array (Nest F A) (inc ds)
nest-cons _∙_ x [] = x ∷ []
nest-cons _∙_ x (y 1∷ ys) = (x ∙ y) 2∷ ys
nest-cons _∙_ x (y 2∷ ys) = x ∷ nest-cons _∙_ y ys

perf-cons : A → Array (Perfect A) ds → Array (Perfect A) (inc ds)
perf-cons = nest-cons _,_
```

# Indexing

Again, we're going to keep things general, allowing multiple index types.
For those index types we'll need a type like `Fin` but for binary numbers.

```agda
data Fin𝔹 (A : Set a) : 𝔹 → Type a where
  here₁ :                       Fin𝔹 A (1ᵇ ∷ ds)
  here₂ : (i : A)             → Fin𝔹 A (2ᵇ ∷ ds)
  there : (i : A) → Fin𝔹 A ds → Fin𝔹 A (d  ∷ ds)

lookup : (∀ {n} → P → T (suc n) → T n)
       → Array T ds
       → Fin𝔹 P ds
       → T 0
lookup ind (x ∷ xs) here₁ = x
lookup ind (x ∷ xs) (here₂ i) = ind i x
lookup ind (x ∷ xs) (there i is) = ind i (lookup ind xs is)

nest-lookup : (∀ {A} → P → F A → A)
            → Array (Nest F A) ds
            → Fin𝔹 P ds
            → A
nest-lookup ind (x ∷ xs) here₁ = x
nest-lookup ind (x ∷ xs) (here₂ i) = ind i x
nest-lookup ind (x ∷ xs) (there i is) = ind i (nest-lookup ind xs is)
```


We'll once more use perfect to show how these generic functions can be
concretised.
For the index types into a perfect tree, we will use a `Bool`.

```agda
perf-lookup : Array (Perfect A) ds → Fin𝔹 Bool ds → A
perf-lookup = nest-lookup (bool fst snd)
```

# Folding

This next function is quite difficult to get right: a fold.
We want to consume the binary array into a unary, cons-list type thing.
Similarly to `foldl` on vectors, we will need to change the return type as we
fold, but we will *also* need to convert from binary to unary, *as we fold*.
The key ingredient is the following function:

```agda
2^_*_ : ℕ → ℕ → ℕ
2^ zero  * n = n
2^ suc m * n = 2* (2^ m * n)
```

It will let us do the type-change-as-you-go trick from `foldl`, but in a binary
setting.
Here's `foldr`:

```agda
array-foldr : (B : ℕ → Type b)
            → (∀ n {m} → T n → B (2^ n * m) → B (2^ n * suc m))
            → B 0 → Array T ds → B ⟦ ds ⇓⟧
array-foldr B c b []        = b
array-foldr B c b (x 1∷ xs) = c 0 x (array-foldr (B ∘ 2*) (c ∘ suc) b xs)
array-foldr B c b (x 2∷ xs) = c 1 x (array-foldr (B ∘ 2*) (c ∘ suc) b xs)
```

And, as you should expect, here's how to use this in combination with the
perfect trees.
Here we'll build a binary random access list from a vector, and convert back to
a vector.

```agda
perf-foldr : (B : ℕ → Type b)
           → (∀ {n} → A → B n → B (suc n))
           → ∀ n {m}
           → Perfect A n
           → B (2^ n * m)
           → B (2^ n * suc m)
perf-foldr B f zero = f
perf-foldr B f (suc n) =
  perf-foldr (B ∘ 2*) (λ { (x , y) zs → f x (f y zs) }) n

toVec : Array (Perfect A) ds → Vec A ⟦ ds ⇓⟧
toVec = array-foldr (Vec _) (perf-foldr (Vec _) _∷_) []

fromVec : Vec A n → Array (Perfect A) ⟦ n ⇑⟧
fromVec = vec-foldr (Array (Perfect _) ∘ ⟦_⇑⟧) perf-cons []
```

# Lenses

That's the end of the "simple" stuff!
The binary random-access list I've presented above is about as simple as I can
get it.

In this section, I want to look at some more complex (and more fun) things you
can do with it.
First: lenses.

Lenses aren't super ergonomic in dependently-typed languages, but they do come
with some advantages.
The lens laws are quite strong, for instance, meaning that often by constructing
programs using a lot of lenses gives us certain properties "for free".
Here, for instance, we can define the lenses for indexing.

```agda
open import Lenses
```

<details>
<summary>Lenses into the head and tail of an array</summary>

```agda
head : Lens (Array T (d ∷ ds)) (T (bool 0 1 d))
head .into (x ∷ _ ) .get = x
head .into (_ ∷ xs) .set x = x ∷ xs
head .get-set (_ ∷ _) _ = refl
head .set-get (_ ∷ _) = refl
head .set-set (_ ∷ _) _ _ = refl

tail : Lens (Array T (d ∷ ds)) (Array (T ∘ suc) ds)
tail .into (_ ∷ xs) .get = xs
tail .into (x ∷ _ ) .set xs = x ∷ xs
tail .get-set (_ ∷ _) _ = refl
tail .set-get (_ ∷ _) = refl
tail .set-set (_ ∷ _) _ _ = refl
```

</details>

```agda
nest-lens : (∀ {A} → P → Lens (F A) A)
          → Fin𝔹 P ds
          → Lens (Array (Nest F A) ds) A
nest-lens ln here₁        = head
nest-lens ln (here₂ i)    = head ⋯ ln i
nest-lens ln (there i is) = tail ⋯ nest-lens ln is ⋯ ln i
```

<details>
<summary>Top-down version</summary>

```agda
ind-lens : (∀ {n} → P → Lens (T (suc n)) (T n))
         → Fin𝔹 P ds
         → Lens (Array T ds) (T 0)
ind-lens ln here₁        = head
ind-lens ln (here₂ i)    = head ⋯ ln i
ind-lens ln (there i is) = tail ⋯ ind-lens ln is ⋯ ln i
```

</details>

# Fenwick Trees

Finally, to demonstrate some of the versatility of this data structure, we're
going to implement a tree based on a *fenwick* tree.
This is a data structure for prefix sums: we can query the running total at any
point, and *update* the value at a given point, in $\mathcal{O}(\log n)$ time.
We're going to make it generic over a monoid:

```agda
module _ {ℓ} (mon : Monoid ℓ) where
  open Monoid mon

  record Leaf : Set ℓ where
    constructor leaf
    field val : 𝑆
  open Leaf

  mutual
    SumNode : ℕ → Set ℓ
    SumNode zero = Leaf
    SumNode (suc n) = Summary n × Summary n

    Summary : ℕ → Set ℓ
    Summary n = Σ 𝑆 (fiber (cmb n))

    cmb : ∀ n → SumNode n → 𝑆
    cmb zero = val
    cmb (suc _) (x , y) = fst x ∙ fst y

  Fenwick : 𝔹 →  Set ℓ
  Fenwick = Array Summary
```

So it's an aray of perfect trees, with each branch in the tree containing a
summary of its children.
Constructing a tree is straightforward:

```agda
  comb : ∀ n → Summary n → Summary n → Summary (suc n)
  comb n xs ys = _ , (xs , ys) , refl

  sing : 𝑆 → Summary 0
  sing x = _ , leaf x , refl

  fFromVec : Vec 𝑆 n → Fenwick ⟦ n ⇑⟧
  fFromVec = vec-foldr (Fenwick ∘ ⟦_⇑⟧) (cons comb ∘ sing) []
```

Updating a particular point involves a good bit of boilerplate, but isn't too
complex.

<details>
<summary>Lenses into a single level of the tree</summary>

```agda
  upd-lens : Bool → Lens (Summary (suc n)) (Summary n)
  upd-lens false .into (_ , (x , y) , _) .get = x
  upd-lens false .into (_ , (_ , y) , _) .set x = _ , (x , y) , refl
  upd-lens true  .into (_ , (x , y) , _) .get = y
  upd-lens true  .into (_ , (x , _) , _) .set y = _ , (x , y) , refl
  upd-lens false .get-set _ _ = refl
  upd-lens true  .get-set _ _ = refl
  upd-lens false .set-get (t , xs , p) i .fst = p i
  upd-lens false .set-get (t , xs , p) i .snd .fst = xs
  upd-lens false .set-get (t , xs , p) i .snd .snd j = p (i ∧ j)
  upd-lens true  .set-get (t , xs , p) i .fst = p i
  upd-lens true  .set-get (t , xs , p) i .snd .fst = xs
  upd-lens true  .set-get (t , xs , p) i .snd .snd j = p (i ∧ j)
  upd-lens false .set-set _ _ _ = refl
  upd-lens true  .set-set _ _ _ = refl

  top : Lens (Summary 0) 𝑆
  top .into x .get = x .snd .fst .val
  top .into x .set y .fst = y
  top .into x .set y .snd .fst .val = y
  top .into x .set y .snd .snd = refl
  top .get-set _ _ = refl
  top .set-get (x , y , p) i .fst = p i
  top .set-get (x , y , p) i .snd .fst = y
  top .set-get (x , y , p) i .snd .snd j = p (i ∧ j)
  top .set-set _ _ _ = refl
```

</details>

```agda
  update : Fin𝔹 Bool ds → Lens (Fenwick ds) 𝑆
  update is = ind-lens upd-lens is ⋯ top
```

Finally, here's how we get the summary up to a particular point in
$\mathcal{O}(\log n)$ time:

```agda
  running : (∀ n → Bool → T (suc n) → 𝑆 × T n)
          → (∀ n → T n → 𝑆)
          → Array T ds
          → Fin𝔹 Bool ds
          → 𝑆 × T 0
  running l s (x ∷ xs) (there i is) =
    let y , ys = running (l ∘ suc) (s ∘ suc) xs is
        z , zs = l _ i ys
    in s _ x ∙ y ∙ z , zs
  running l s (x 1∷ xs) here₁ = ε , x
  running l s (x 2∷ xs) (here₂ i) = l _ i x

  prefix : Fenwick ds → Fin𝔹 Bool ds → 𝑆
  prefix xs is = let ys , zs , _ = running ind (λ _ → fst) xs is in ys ∙ zs
    where
    ind : ∀ n → Bool → Summary (suc n) → 𝑆 × Summary n
    ind n false (_ , (xs , _) , _) = ε , xs
    ind n true  (_ , ((x , _) , (y , ys)) , _) = x , (y , ys)
```
