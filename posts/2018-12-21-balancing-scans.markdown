---
title: Balancing Scans
tags: Haskell, Agda
series: Balanced Folds
bibliography: Tree Folds.bib
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

# Magical Speedups

The fold above is kind of magical: for a huge class of algorithms, it kind of
"automatically" improves some factor of theirs from $\mathcal{O}(n)$ to
$\mathcal{O}(\log n)$. For instance: to sum a list of floats, `foldl' (+)
0`{.haskell} will have an error growth of $\mathcal{O}(n)$; `treeFold (+) 0`,
though, has an error rate of $\mathcal{O}(\log n)$. Similarly, using the
following function to merge two sorted lists:

```haskell
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge (x:xs) ys = go x xs ys
  where
    go x xs [] = x : xs
    go x xs (y:ys)
      | x <= y    = x : go y ys xs
      | otherwise = y : go x xs ys
```

We get either insertion sort ($\mathcal{O}(n^2)$) or merge sort ($\mathcal{O}(n
\log n)$) just depending on which fold you use.

```haskell
foldr    merge [] . map pure -- n^2
treeFold merge [] . map pure -- n log(n)
```

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
  infixr 5 _⊛_ 2^_×_⊛_

  2^_×_⊛_ : ℕ → A → Tree A → Tree A
  2^ n × x ⊛ 2^ suc m × y + ys = 2^ n × x + ⟨ 2^ m × y + ys ⟩
  2^ n × x ⊛ 2^ zero  × y + ⟨⟩ = 2^ suc n × (x * y) + ⟨⟩
  2^ n × x ⊛ 2^ zero  × y + ⟨ ys ⟩ = 2^ suc n × (x * y) ⊛ ys

  _⊛_ : A → Tree A → Tree A
  _⊛_ = 2^ 0 ×_⊛_

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

  _∪_ : ∀ {b} → Ordered b → Ordered b → Ordered b
  [] ∪ ys = ys
  (x ∷ xs) ∪ ys = ⟅ x ∹ xs ∪ ys ⟆
    where
    ⟅_∹_∪_⟆ : ∀ {b} → ∀ x ⦃ _ : x ≥ b ⦄ → Ordered [ x ] → Ordered b → Ordered b
    ⟅_∪_∹_⟆ : ∀ {b} → Ordered b → ∀ y ⦃ _ : y ≥ b ⦄ → Ordered [ y ] → Ordered b
    merge : ∀ {b} x y ⦃ _ : x ≥ b ⦄ ⦃ _ : y ≥ b ⦄
          → Total _≤_ x y
          → Ordered [ x ]
          → Ordered [ y ]
          → Ordered b

    ⟅ x ∹ xs ∪ [] ⟆ = x ∷ xs
    ⟅ x ∹ xs ∪ y ∷ ys ⟆ = merge x y (x ≤? y) xs ys
    ⟅ [] ∪ y ∹ ys ⟆ = y ∷ ys
    ⟅ x ∷ xs ∪ y ∹ ys ⟆ = merge x y (x ≤? y) xs ys

    merge x y x≤y xs ys = x ∷ ⟅ xs ∪ y ∹ ys ⟆
    merge x y y≤x xs ys = y ∷ ⟅ x ∹ xs ∪ ys ⟆


  open TreeFold

  sort : List A → Ordered ⊥
  sort = ⦅ _∪_ , [] ⦆ ∘ map (_∷ [])
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
  treeFoldHom _○_ ∎ assoc *⟨_⟩ b = foldr-fusion _○_ ∎ ⟦_⟧↓ ⟦ b ⟧↑ *⟨_⟩ (⊛-hom zero)
    where
    ⊛-hom : ∀ n x xs → ⟦ 2^ n × x ⊛ xs ⟧↓ ≈ x * ⟦ xs ⟧↓
    ⊛-hom n x (2^ suc m × y + ⟨⟩    ) = ∎
    ⊛-hom n x (2^ suc m × y + ⟨ ys ⟩) = ∎
    ⊛-hom n x (2^ zero  × y + ⟨⟩    ) = ∎
    ⊛-hom n x (2^ zero  × y + ⟨ ys ⟩) = ⊛-hom (suc n) (x * y) ys ○ assoc x y ⟦ ys ⟧↓
```

# "Implicit" Data Structures

Consider the following implementation of the tree above in Haskell:

```haskell
type Tree a = [(Int,a)]

cons :: (a -> a -> a) -> a -> Tree a -> Tree a
cons (*) = cons' 0 
  where
    cons' n x [] = [(n,x)]
    cons' n x ((0,y):ys) = cons' (n+1) (x * y) ys
    cons' n x ((m,y):ys) = (n,x) : (m-1,y) : ys
```

The `cons` function "increments" that list as if it were the bits of a binary
number. Now, consider using the `merge` function from above, in a pattern like
this:

```haskell
f = foldr (cons merge . pure) []
```

What does `f` build? A list of lists, right?


Kind of. That's what's built in terms of the observable, but what's actually
stored in memory us a bunch of thunks. The shape of *those* is what I'm
interested in. We can try and see what they look like by using a data structure
that doesn't force on merge:

```haskell
data Tree a = Leaf a | Tree a :*: Tree a

f = foldr (cons (:*:) . Leaf) []
```

Using a handy tree-drawing function, we can see what `f [1..13]` looks like:

```
[(0,*),(1,*),(0,*)]
    └1    │ ┌2  │  ┌6
          │┌┤   │ ┌┤
          ││└3  │ │└7
          └┤    │┌┤
           │┌4  │││┌8
           └┤   ││└┤
            └5  ││ └9
                └┤
                 │ ┌10
                 │┌┤
                 ││└11
                 └┤
                  │┌12
                  └┤
                   └13
```

It's a binomial heap! It's a list of trees, each one contains $2^n$ elements.
But they're not in heap order, you say? Well, as a matter of fact, they *are*.
It just hasn't been evaluated yet. Once we force---say---the first element, the
rest will shuffle themselves into a tree of thunks.

This illustrates a pretty interesting similarity between binomial heaps and
merge sort. Performance-wise, though, there's another interesting property: the
thunks *stay thunked*. In other words, if we do a merge sort via:

```haskell
sort = foldr (merge . snd) [] . foldr (cons merge . pure) []
```

We could instead freeze the fold, and look at it at every point:

```haskell
sortPrefixes = map (foldr (merge . snd) []) . scanl (flip (cons merge . pure)) []
>>> [[],[1],[1,4],[1,2,4],[1,2,3,4],[1,2,3,4,5]]
```

And `sortPrefixes` is only $\mathcal{O}(n^2)$ (rather than $\mathcal{O}(n^2 \log
n)$). I confess I don't know of a use for sorted prefixes, but it should
illustrate the general idea: we get a pretty decent batching of operations, with
the ability to freeze at any point in time. The other nice property (which I
mentioned in the last post) is that any of the tree folds are extremely
parallel.

# Random Shuffles

[There's a great article on shuffling in
Haskell](http://okmij.org/ftp/Haskell/AlgorithmsH.html#perfect-shuffle) which
provides an $\mathcal{O}(n \log n)$ implementation of a perfect random shuffle.
Unfortunately, the [Fisher-Yates
shuffle](https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle) isn't
applicable in a pure functional setting, so you have to be a little cleverer.

The first implementation most people jump to (certainly the one I thought of) is
to assign everything in the sequence a random number, and then sort according to
that number. Perhaps surprisingly, this *isn't* perfectly random! It's a little
weird, but the example in the article explains it well: basically, for $n$
elements, your random numbers will have $n^n$ possible values, but the output of
the sort will have $n!$ possible values. Since they don't divide into each other
evenly, you're going to have some extra weight on some permutations, and less on
others.

Instead, we can generate a random
[*factoradic*](https://en.wikipedia.org/wiki/Factorial_number_system) number. A
factoradic number is one where the $n$th digit is in base $n$. Because of this,
a factoradic number with $n$ digits has $n!$ possible values: exactly what we
want.

In the article, the digits of the number are used to pop values from a binary
tree. Because the last digit will have $n$ possible values, and the second last
$n-1$, and so on, you can keep popping without hitting an empty tree.

This has the correct time complexity---$\mathcal{O}(n \log n)$---but there's a
lot of overhead. Building the tree, then indexing into it, the rebuilding after
each pop, etc.

We'd *like* to just sort the list, according to the indices. The problem is that
the indices are relative: if you want to `cons` something onto the list, you
have to increment the rest of the indices, as they've all shifted right by one.

What we'll do instead is use the indices as *gaps*. Our merge function looks
like the following:

```haskell
merge [] ys = ys
merge xs [] = xs
merge ((x,i):xs) ((y,j):ys)
  | i <= j    = (x,i) : merge xs ((y,j-i):ys)
  | otherwise = (y,j) : merge ((x,i-j-1):xs) ys
```

With that, and the same `cons` as above, we get a very simple random shuffle
algorithm:

```haskell
shuffle xs = map fst
           . foldr (merge . snd) []
           . foldr f (const []) xs
  where
    f x xs (i:is) = cons merge [(x,i)] (xs is)
```

The other interesting thing about this algorithm is that it can use Peano
numbers with taking too much of a performance hit:

```haskell
merge : ∀ {a} {A : Set a} → List (A × ℕ) → List (A × ℕ) → List (A × ℕ)
merge xs [] = xs
merge {A = A} xs ((y , j) ∷ ys) = go-r xs y j ys
  where
  go-l : A → ℕ → List (A × ℕ) → List (A × ℕ) → List (A × ℕ)
  go-r : List (A × ℕ) → A → ℕ → List (A × ℕ) → List (A × ℕ)
  go : ℕ → ℕ → A → ℕ → List (A × ℕ) → A → ℕ → List (A × ℕ) → List (A × ℕ)

  go i     zero   x i′ xs y j′ ys = (y , j′) ∷ go-l x i xs ys
  go zero (suc j) x i′ xs y j′ ys = (x , i′) ∷ go-r xs y j ys
  go (suc i) (suc j) = go i j

  go-l x i xs [] = (x , i) ∷ xs
  go-l x i xs ((y , j) ∷ ys) = go i j x i xs y j ys

  go-r [] y j ys = (y , j) ∷ ys
  go-r ((x , i) ∷ xs) y j ys = go i j x i xs y j ys

shuffle : ∀ {a} {A : Set a} → List A → List ℕ → List A
shuffle {a} {A} xs i = map proj₁ (⦅ [] , zip-inds xs i ⦆)
  where
  open TreeFold {a} {List (A × ℕ)} merge

  zip-inds : List A → List ℕ → List (List (A × ℕ))
  zip-inds [] inds = []
  zip-inds (x ∷ xs) [] = ((x , 0) ∷ []) ∷ zip-inds xs []
  zip-inds (x ∷ xs) (i ∷ inds) = ((x , i) ∷ []) ∷ zip-inds xs inds
```

I don't know exactly what the complexity of this is, but I *think* it should be
better than the usual approach of popping from a vector.

# Future Stuff

This is just a collection of random thoughts for now, but I intend to work on
using these folds to see if there are any other algorithms they can be useful
for. In particular, I think I can write a version of Data.List.permutations
which benefits from sharing. And I'm interested in using the implicit binomial
heap for some search problems.
