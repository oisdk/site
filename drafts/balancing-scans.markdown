---
title: Balancing Scans
tags: Haskell, Agda
---

[Previously](2017-10-30-balancing-folds.html) I tried to figure out a way to
fold lists in a more balanced way. Usually, when folding lists, you've got two
choices for your folds, both of which are extremely unbalanced in one direction
or another. Jon Fairbairn
[wrote](https://www.mail-archive.com/haskell@haskell.org/msg01788.html) a more
balanced version, which looked something like this:

```haskell
treeFold :: (a -> a -> a) -> a -> [a] -> a
treeFold f = go
  where
    go x [] = x
    go a (b:l) = go (f a b) (pairMap l)
    pairMap (x:y:rest) = f x y : pairMap rest
    pairMap xs = xs
```

# What's the use?

The fold above is kind of magical: for a huge class of algorithms, it kind of
"automatically" improves some factor of theirs from $\mathcal{O}(n)$ to
$\mathcal{O}(\log n)$. For instance: to sum a list of floats, `foldl' (+)
0`{.haskell} will have an error growth of $\mathcal{O}(n)$; `treeFold (+) 0`,
though, has an error rate of $\mathcal{O}(\log n)$. Similarly, using the
following function to merge two sorted lists:

```haskell
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge xs@(x:xs') ys@(y:ys')
  | x <= y    = x : merge xs' ys
  | otherwise = y : merge xs ys'
```

Then `foldr merge [] . map pure` is insertion sort (and therefore
$\mathcal{O}(n^2)$), whereas `treeFold merge [] . map pure` is merge sort, and
therefore $\mathcal{O}(n \log n)$.

I'll give some more examples later, but effectively it gives us a better
"divide" step in many divide and conquer algorithms.

# Termination

As it was such a useful fold, and so integral to many tricky algorithms, I
really wanted to have it available in Agda. Unfortunately, though, the functions
(as defined above) aren't structurally terminating, and there doesn't *look*
like there's an obvious way to make it so. I tried to make well founded
recursion work, but the proofs were ugly and slow. 

However, we can use some structures from a [previous
post](2018-11-20-fast-verified-structures.html): the nested binary sequence, for
instance. It has some extra nice properties: instead of nesting the types, we
can just apply the combining function.

```agda

mutual
  data Tree {a} (A : Set a) : Set a where
    2^_×_+_ : ℕ → A → Node A → Tree A

  data Node {a} (A : Set a) : Set a where
    ⟨⟩  : Node A
    ⟨_⟩ : Tree A → Node A

module TreeFold {a} {A : Set a} (_*_ : A → A → A) where
  infixr 5 _⊛_ 2^_×_⊛′_ 2^_×_⊛″_

  2^_×_⊛′_ : ℕ → A → Tree A → Tree A
  2^_×_⊛″_ : ℕ → A → Node A → Tree A

  2^ n × x ⊛′ 2^ 0     × y + ys = 2^ suc n × x * y ⊛″ ys
  2^ n × x ⊛′ 2^ suc m × y + ys = 2^ n × x + ⟨ 2^ m × y + ys ⟩

  2^ n × x ⊛″ ⟨⟩     = 2^ n × x + ⟨⟩
  2^ n × x ⊛″ ⟨ xs ⟩ = 2^ n × x ⊛′ xs

  _⊛_ : A → Tree A → Tree A
  _⊛_ = 2^ 0 ×_⊛′_

  ⟦_⟧↓ : Tree A → A
  ⟦ 2^ _ × x + ⟨⟩ ⟧↓ = x
  ⟦ 2^ _ × x + ⟨ xs ⟩ ⟧↓ = x * ⟦ xs ⟧↓

  ⟦_⟧↑ : A → Tree A
  ⟦ x ⟧↑ = 2^ 0 × x + ⟨⟩

  ⦅_,_⦆ : A → List A → A
  ⦅ x , xs ⦆ = ⟦ foldr _⊛_ ⟦ x ⟧↑ xs ⟧↓
```

Alternatively, we can get $\mathcal{O}(1)$ cons with the skew array:

```agda
infixr 5 _⊛_
_⊛_ : A → Tree A → Tree A
x ⊛ 2^ n × y  + ⟨⟩ = 2^ 0 × x + ⟨ 2^ n × y + ⟨⟩ ⟩
x ⊛ 2^ n × y₁ + ⟨ 2^ 0     × y₂ + ys ⟩ = 2^ suc n × (x * (y₁ * y₂)) + ys
x ⊛ 2^ n × y₁ + ⟨ 2^ suc m × y₂ + ys ⟩ = 2^ 0 × x + ⟨ 2^ n × y₁ + ⟨ 2^ m × y₂ + ys ⟩ ⟩
```

Using this, a proper and efficient merge sort is very straightforward:

```agda
module Sorting
  {a e l}
  (strictTotalOrder : StrictTotalOrder a e l)
  where
  open StrictTotalOrder strictTotalOrder

  merge : List Carrier → List Carrier → List Carrier
  merge [] ys = ys
  merge (x ∷ xs) ys = merge₁ x xs ys
    where
    merge₁ : Carrier → List Carrier → List Carrier → List Carrier
    merge₂ : ∀ x y
           → Tri (x < y) (x ≈ y) (y < x)
           → List Carrier
           → List Carrier
           → List Carrier

    merge₁ x xs [] = x ∷ xs
    merge₁ x xs (y ∷ ys) = merge₂ x y (compare x y) xs ys

    merge₂ x y (tri< a ¬b ¬c) xs ys = x ∷ merge₁ y ys xs
    merge₂ x y (tri≈ ¬a b ¬c) xs ys = x ∷ y ∷ merge xs ys
    merge₂ x y (tri> ¬a ¬b c) xs ys = y ∷ merge₁ x xs ys

  open TreeFold

  sort : List Carrier → List Carrier
  sort = ⦅ merge , [] ⦆ ∘ List.map List.[_]
```

# Validity

It would be nice if we could verify these optimizated versions of folds.
Luckily, since they use `foldr` in their implementations, verification can rely
on `foldr` fusion:

```agda
module Proofs
  {a r}
  {A : Set a}
  {_≈_ : Rel A r}
  where

  open import Algebra.FunctionProperties _≈_

  foldr-universal : Transitive _≈_
                  → ∀ {b} {B : Set b} (h : List B → A) f e
                  → ∀[ f ⊢ Congruent₁ ]
                  → (h [] ≈ e)
                  → (∀ x xs → h (x ∷ xs) ≈ f x (h xs))
                  → ∀ xs → h xs ≈ foldr f e xs
  foldr-universal _○_ h f e f⟨_⟩ ⇒[] ⇒_∷_ [] = ⇒[]
  foldr-universal _○_ h f e f⟨_⟩ ⇒[] ⇒_∷_ (x ∷ xs) =
    (⇒ x ∷ xs) ○ f⟨ foldr-universal _○_ h f e f⟨_⟩ ⇒[] ⇒_∷_ xs ⟩

  foldr-fusion : Transitive _≈_
               → Reflexive _≈_
               → ∀ {b c} {B : Set b} {C : Set c} (h : C → A) {f : B → C → C} {g : B → A → A} (e : C)
               → ∀[ g ⊢ Congruent₁ ]
               → (∀ x y → h (f x y) ≈ g x (h y))
               → ∀ xs → h (foldr f e xs) ≈ foldr g (h e) xs
  foldr-fusion _○_ ∎ h {f} {g} e g⟨_⟩ fuse =
    foldr-universal _○_ (h ∘ foldr f e) g (h e) g⟨_⟩ ∎ (λ x xs → fuse x (foldr f e xs))

  module _ {_*_ : A → A → A} where
    open TreeFold _*_

    treeFoldHom : Transitive _≈_
                → Reflexive _≈_
                → Associative _*_
                → RightCongruent _*_
                → ∀ x xs
                → ⦅ x , xs ⦆ ≈ foldr _*_ x xs
    treeFoldHom _○_ ∎ assoc *⟨_⟩ b = foldr-fusion _○_ ∎ ⟦_⟧↓ ⟦ b ⟧↑ *⟨_⟩ ⊛-hom
      where
      ⊛-hom : ∀ x xs → ⟦ x ⊛ xs ⟧↓ ≈ (x * ⟦ xs ⟧↓)
      ⊛-hom x (2^ n × y  + ⟨⟩) = ∎
      ⊛-hom x (2^ n × y₁ + ⟨ 2^ zero  × y₂ + ⟨⟩     ⟩) = ∎
      ⊛-hom x (2^ n × y₁ + ⟨ 2^ zero  × y₂ + ⟨ ys ⟩ ⟩) = assoc x (y₁ * y₂) ⟦ ys ⟧↓ ○ *⟨ assoc y₁ y₂ ⟦ ys ⟧↓ ⟩
      ⊛-hom x (2^ n × y₁ + ⟨ 2^ suc m × y₂ + ⟨⟩     ⟩) = ∎
      ⊛-hom x (2^ n × y₁ + ⟨ 2^ suc m × y₂ + ⟨ ys ⟩ ⟩) = ∎
```
