---
title: Concatenative Programming; The Free Monoid of Programming Languages
tags: Concatenative
---


Point-free style is one of the distinctive markets of functional programming
languages.
Want to sum a list?
That's as easy as:

```haskell
sum = foldr (+) 0
```

Now I want to sum every number after adding one to it.

```haskell
sumSuccs = foldr (+) 0 . map ((+) 1)
```

One more step to make this function truly abstract™ and general™: we'll allow
the user to supply their own number to add

```haskell
sumAdded = foldr (+) 0 . map . (+)
```

And here the trouble begins.
The above expression won't actually type check.
In fact, it'll give a pretty terrible error message:

```
• Non type-variable argument in the constraint: Num [a]
  (Use FlexibleContexts to permit this)
• When checking the inferred type
    sumThoseThat :: forall a.
                    (Num [a], Foldable ((->) [a])) =>
                    a -> [a]
```

I remember as a beginner being confused by similar messages.
What's `FlexibleContexts`?
I had thought that the "point-free style" just meant removing the last variable
from an expression if it's also the last argument:

```haskell
sum xs = foldr (+) 0 xs
sum = foldr (+) 0
```

Why doesn't it work here?

Well, it doesn't work because the types don't line up, but I'm going to try and
explain a slightly different perspective on the problem, which is
*associativity*.

To make it a little clearer, let's see
what happens when we point-fill the expression:

```haskell
sumAdded n xs = (foldr(+) 0 . (map . (+))) n xs
             => foldr(+) 0 ((map . (+)) n) xs
             => foldr(+) 0 (map ((+) n)) xs
```

Indeed, the problem is the placement of the parentheses.
What we want at the end is:
```haskell
             => foldr(+) 0 (map ((+) n) xs)
```

But, no matter.
We have to jiggle the arguments around, or we could use something terrible like
this:

```haskell
infixr 9 .:
(.:) = (.).(.)

sumAdded = foldr (+) 0 .: map . (+)
```

Is there something, though, that could do this automatically?

# Associativity

We run into a similar problem in Agda.
We're forever having to prove statements like:

```agda
(x + y) + z ≡ x + (y + z)
x ≡ x + 0
```

There are a couple of ways to get around the issue, and for monoids there's a
rich theory of techniques.
I'll just show one for now, which relies on the *endomorphism* monoid.
This monoid is created by partially applying the monoid's binary operator:

```agda
Endo : Set
Endo = ℕ → ℕ

⟦_⇑⟧ : ℕ → Endo
⟦ n ⇑⟧ m = n + m
```

And you can get back to the underlying monoid by applying it to the neutral
element:

```agda
⟦_⇓⟧ : Endo → ℕ
⟦ n ⇓⟧ = n 0
```

Here's the important parts: first, we can lift the underlying operation into the
endomorphism:

```agda
_⊕_ : Endo → Endo → Endo
xs ⊕ ys = λ x → xs (ys x)

⊕-homo : ∀ n m → ⟦ ⟦ n ⇑⟧ ⊕ ⟦ m ⇑⟧ ⇓⟧ ≡ n + m
⊕-homo n m = cong (n +_) (+-identityʳ m)
```

And second, it's *definitionally* associative.

```agda
⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
⊕-assoc _ _ _ = refl
```

These are all clues as to how to solve the composition problem in the Haskell
code above.
We need definitional associativity, somehow.
Maybe we can get it from the endomorphism monoid?

# State

You're probably familiar with Haskell's state monad:

```haskell
newtype State s a = State { runState :: s -> (a, s) }
```

It can help a lot when you're threading around fiddly accumulators and so on.

```haskell
nub :: Ord a => [a] -> [a]
nub = go Set.empty
  where
    go seen [] = []
    go seen (x:xs)
      | x `Set.member` seen = go seen xs
      | otherwise = x : go (Set.insert x seen) xs
```

```haskell
nub :: Ord a => [a] -> [a]
nub = flip evalState Set.empty . go
  where
    go [] = pure []
    go (x:xs) = do
        seen <- gets (Set.member x)
        if seen
          then go xs
          else do
              modify (Set.insert x)
              (x:) <$> go xs
```

Of course, these days state is a transformer:

```haskell
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }
```

This lets us stack multiple effects on top of each other: error handling, IO,
randomness, even another state monad.
In fact, if you *do* stack another state monad on top, you might be surprised by
the efficiency of the code it generates:

```haskell
type DoubleState s1 s2 a = StateT s1 (State s2) a
                        => s1 -> State s2 (a, s1)
                        => s1 -> s2 -> ((a, s1), s2)
```

It's nothing earth shattering, but it inlines and optimises well.
That output is effectively a left-nested list, also.
