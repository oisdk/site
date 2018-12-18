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
data Total {a r} {A : Set a} (_≤_ : A → A → Set r) (x y : A) : Set (a ⊔ r) where
  x≤y : ⦃ _ : x ≤ y ⦄ → Total _≤_ x y
  y≤x : ⦃ _ : y ≤ x ⦄ → Total _≤_ x y

module Sorting {a r}
               {A : Set a}
               {_≤_ : A → A → Set r}
               (_≤?_ : ∀ x y → Total _≤_ x y) where
  data [∙] : Set a where
    ⊥   : [∙]
    [_] : A → [∙]

  data _≥_ (x : A) : [∙] → Set (a ⊔ r) where
    instance ⌈_⌉ : ∀ {y} → y ≤ x → x ≥ [ y ]
    instance ⌊⊥⌋ : x ≥ ⊥

  infixr 5 _∷_
  data Ordered (b : [∙]) : Set (a ⊔ r) where
    []  : Ordered b
    _∷_ : ∀ x → ⦃ x≥b : x ≥ b ⦄ → (xs : Ordered [ x ]) → Ordered b

  merge : ∀ {b} → Ordered b → Ordered b → Ordered b
  merge [] ys = ys
  merge (x ∷ xs) ys = merge′ x xs ys
    where
    merge′ : ∀ {b} x → ⦃ _ : x ≥ b ⦄ → Ordered [ x ] → Ordered b → Ordered b
    merge′ x xs [] = x ∷ xs
    merge′ x xs (y ∷ ys) with x ≤? y
    ... | y≤x = y ∷ merge′ x xs ys
    ... | x≤y = x ∷ merge′ y ys xs

  open TreeFold

  sort : List A → Ordered ⊥
  sort = ⦅ merge , [] ⦆ ∘ List.map λ x → x ∷ []
```

# Validity

It would be nice if we could verify these optimizated versions of folds.
Luckily, by writing them using `foldr`, we've stumbled into well-trodden ground:
the *foldr fusion law*. It states that if you have some transformation $f$, and
two binary operators $\oplus$ and $\otimes$, then: 

\begin{align}
   f (x \oplus y)                         &&=\;& x \otimes f y \\
   \implies f \circ \text{foldr} \oplus e &&=\;& \text{foldr} \otimes (f e)
\end{align}

This fits right in with the function we used above. $f$ is `⟦_⟧↓`, $\oplus$ is
`_⊛_`, and $\otimes$ is whatever combining function was passed in. Let's prove
the foldr fusion law, then, before we go any further.

```agda
module Proofs
  {a r}
  {A : Set a}
  {R : Rel A r}
  where

  infix 4 _≈_
  _≈_ = R

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
               → ∀ {b c} {B : Set b} {C : Set c} (f : C → A) {_⊕_ : B → C → C} {_⊗_ : B → A → A} e
               → ∀[ _⊗_ ⊢ Congruent₁ ]
               → (∀ x y → f (x ⊕ y) ≈ x ⊗ f y)
               → ∀ xs → f (foldr _⊕_ e xs) ≈ foldr _⊗_ (f e) xs
  foldr-fusion _○_ ∎ h {f} {g} e g⟨_⟩ fuse =
    foldr-universal _○_ (h ∘ foldr f e) g (h e) g⟨_⟩ ∎ (λ x xs → fuse x (foldr f e xs))
```

We're not using the proofs in Agda's standard library because these are tied to
propositional equality. In other words, instead of using an abstract binary
relation, they prove things over *actual* equality. That's all well and good,
but as you can see above, we don't need propositional equality: we don't even
need the relation to be an equivalence, we just need transitivity and
reflexivity.

After that, we can state precisely what correspondence the tree fold has, and
under what conditions it does the same things as a fold:

```agda
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
      ⊛-hom : ∀ x xs → ⟦ x ⊛ xs ⟧↓ ≈ x * ⟦ xs ⟧↓
      ⊛-hom x (2^ n × y  + ⟨⟩) = ∎
      ⊛-hom x (2^ n × y₁ + ⟨ 2^ zero  × y₂ + ⟨⟩     ⟩) = ∎
      ⊛-hom x (2^ n × y₁ + ⟨ 2^ zero  × y₂ + ⟨ ys ⟩ ⟩) = assoc x (y₁ * y₂) ⟦ ys ⟧↓ ○ *⟨ assoc y₁ y₂ ⟦ ys ⟧↓ ⟩
      ⊛-hom x (2^ n × y₁ + ⟨ 2^ suc m × y₂ + ⟨⟩     ⟩) = ∎
      ⊛-hom x (2^ n × y₁ + ⟨ 2^ suc m × y₂ + ⟨ ys ⟩ ⟩) = ∎
```
