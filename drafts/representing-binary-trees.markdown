---
title: Representing Binary Trees
---

```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Posts.RepresentingBinaryTrees where

open import Level
open import Agda.Builtin.Nat using (suc; zero) renaming (Nat to ℕ)
open import Agda.Builtin.List
open import Function using (id; _∘_)

variable
  n m : ℕ

```

I've been playing around with some interesting algorithms and aspects of binary
trees.

```agda
data Tree : Type₀ where
  ∙   : Tree
  _*_ : Tree → Tree → Tree

_ : Tree
_ = ∙ * (∙ * ∙)

_ : Tree
_ = (∙ * ∙) * ∙
```

I thought I'd go through some of them today!

# Enumerating

Apparently enumeration of binary trees is a very well-studied and important
algorithm in combinatorics.
I came across it while trying to write a verified implementation of the
countdown problem: this is the puzzle of writing an algroithm to solve
[countdown](https://en.wikipedia.org/wiki/Countdown_(game_show)#Numbers_round).
Part of my solution involved enumerating all of the expressions one could
generate from a list of numbers; this, in turn, required me to enumerate all of
the binary trees of a given size.

This turns out to not be an easy problem at all!
Attempting to do it directly was a headache: in particular it was nearly
impossible to prove termination.

So instead I decided to try and figure out a representation for binary trees
which was easier to generate and enumerate.
So I turned to Dyck words.

# Dyck Words

Dyck words are strings of balanced parentheses.

    ()()()
    (()())
    ((()())())

It turns out that these simple strings are isomorphic to binary trees.
What's more, it seems like it would be easier to enumerate strings of balances
parentheses than it would be to enumerate the trees.

In order to prove it, we'll need to figure out a *type* for these strings.
Here's one:

```agda
infixr 5 ⟨_ ⟩_
data Dyck : ℕ → ℕ → Type₀ where
  done : Dyck zero zero
  ⟨_ : Dyck (suc n) m → Dyck n (suc m)
  ⟩_ : Dyck n       m → Dyck (suc n) m
```

It has two parameters, one representing the amount of extraneous closing parens
left over, the other representing the total number of closed pairs.
Semantically, it represents *suffixes* of Dyck words; a value of type `Dyck 0 n`
represents a full Dyck word.

```agda
_ : Dyck zero 3
_ = ⟨ ⟩ ⟨ ⟩ ⟨ ⟩ done

_ : Dyck zero 3
_ = ⟨ ⟨ ⟩ ⟨ ⟩ ⟩ done

_ : Dyck zero 5
_ = ⟨ ⟨ ⟨ ⟩ ⟨ ⟩ ⟩ ⟨ ⟩ ⟩ done
```



```agda
support-dyck : ∀ n m → List (Dyck n m)
support-dyck = λ n m → sup-k n m id []
  module ListDyck where
  open import Data.List using (_∷_; [])

  Diff : Type₀ → Type₁
  Diff A = ∀ {B : Type₀} → (A → B) → List B → List B

  mutual
    sup-k : ∀ n m → Diff (Dyck n m)
    sup-k n m k = end n m k ∘ lefts n m k ∘ rights n m k

    lefts : ∀ n m → Diff (Dyck n m)
    lefts n zero    k = id
    lefts n (suc m) k = sup-k (suc n) m (k ∘ ⟨_)

    rights : ∀ n m → Diff (Dyck n m)
    rights (suc n) m k = sup-k n m (k ∘ ⟩_)
    rights zero    m k = id

    end : ∀ n m → Diff (Dyck n m)
    end (suc _) _    k = id
    end zero (suc _) k = id
    end zero zero    k xs = k done ∷ xs
```

