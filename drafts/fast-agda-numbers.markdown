---
title: Writing a Fast Number Implementation in Agda
tags: Agda
---

I've been messing around with some binary number implementations in Agda
recently and I have come across a few tricks to make the representation work
quickly.
In this post I'll go through a few of those tricks, which might be helpful for
other people writing Agda and struggling through its slowness.

# The Representation

First things first, I'm using zeroless binary numbers as the basic
representation.
They look like the following:

```agda
infixr 8 1ᵇ_ 2ᵇ_
data 𝔹 : Type₀ where
  0ᵇ : 𝔹
  1ᵇ_ 2ᵇ_ : 𝔹 → 𝔹
```

As you can see, this type is basically a list of booleans: it might be tempting,
therefore, to redefine the type in terms of lists and bools:

```agda
𝔹 : Type₀
𝔹 = List Bool

infixr 8 1ᵇ_ 2ᵇ_
pattern 0ᵇ = []
pattern 1ᵇ_ xs = false ∷ xs
pattern 2ᵇ_ xs = true  ∷ xs
```

Unfortunately, though, that will incur a pretty serious performance hit.
Agda tends to slow down when used with complex, nested types: the simple
non-parameterised type we defined first tends to work much faster.

# Conversion

The next 

# Strictness


```agda
infixr 0 _$!_
_$!_ : {A : Type a} {B : A → Type b} → (∀ x → B x) → ∀ x → B x
f $! x = primForce x f
{-# INLINE _$!_ #-}

infixr 0 let-bang
let-bang : {A : Type a} {B : A → Type b} → ∀ x → (∀ x → B x) → B x
let-bang = primForce
{-# INLINE let-bang #-}

syntax let-bang v (λ x → e) = let! x =! v in! e
```

# Defunctionalisation

# Testing Performance
