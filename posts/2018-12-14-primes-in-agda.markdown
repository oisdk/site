---
title: Prime Sieves in Agda
tags: Agda
series: Prime Sieves
---

Prime numbers in Agda are *slow*. First, they're Peano-based, so a huge chunk of
optimizations we might make in other languages are out of the window. Second, we
really often want to *prove* that they're prime, so the generation code has to
carry verification logic with it (I won't do that today, though). And third, as
always in Agda, you have to convince the compiler of termination. With all of
that in mind, let's try and write a (very slow, very basic) prime sieve in Agda.

First, we can make an "array" of numbers that we cross off as we go.

```agda
primes : ∀ n → List (Fin n)
primes zero = []
primes (suc zero) = []
primes (suc (suc zero)) = []
primes (suc (suc (suc m))) = sieve (tabulate (just ∘ Fin.suc))
  where
  cross-off : Fin _ → List (Maybe (Fin _)) → List (Maybe (Fin _))

  sieve : List (Maybe (Fin _)) → List (Fin _)
  sieve [] = []
  sieve (nothing ∷ xs) =         sieve xs
  sieve (just x  ∷ xs) = suc x ∷ sieve (cross-off x xs)

  cross-off p fs = foldr f (const []) fs p
    where
    B = ∀ {i} → Fin i → List (Maybe (Fin (2 + m)))

    f : Maybe (Fin (2 + m)) → B → B
    f _ xs zero    = nothing ∷ xs p
    f x xs (suc y) = x       ∷ xs y
```

Very simple so far: we run through the list, filtering out the multiples of each
prime as we see it. Unfortunately, this won't pass the termination checker. This
recursive call to `sieve` is the problem:

```agda
sieve (just x ∷ xs) = suc x ∷ sieve (cross-off x xs)
```

Agda finds if a function is terminating by checking that at least one argument
gets (structurally) smaller on every recursive call. `sieve` only takes one
argument (the input list), so that's the one that needs to get smaller. In the
line above, if we replaced it with the following:

```agda
sieve (just x ∷ xs) = suc x ∷ sieve xs
```

We'd be good to go: `xs` is definitely smaller than `(just x ∷ xs)`. `cross-off
x xs`, though? The thing is, `cross-off` returns a list of the same length that
it's given. But the function call is opaque: Agda can't automatically see the
fact that the length stays the same. Reaching for a proof here is the wrong
move, though: you can get all of the same benefit by switching out the list for
a length-indexed vector.

```agda
primes : ∀ n → List (Fin n)
primes zero = []
primes (suc zero) = []
primes (suc (suc zero)) = []
primes (suc (suc (suc m))) = sieve (tabulate (just ∘ Fin.suc))
  where
  cross-off : ∀ {n} → Fin _ → Vec (Maybe _) n → Vec (Maybe _) n

  sieve : ∀ {n} →  Vec (Maybe (Fin (2 + m))) n → List (Fin (3 + m))
  sieve [] = []
  sieve (nothing ∷ xs) =         sieve xs
  sieve (just x  ∷ xs) = suc x ∷ sieve (cross-off x xs)

  cross-off p fs = foldr B f (const []) fs p
    where
    B = λ n → ∀ {i} → Fin i → Vec (Maybe (Fin (2 + m))) n

    f : ∀ {n} → Maybe (Fin (2 + m)) → B n → B (suc n)
    f _ xs zero    = nothing ∷ xs p
    f x xs (suc y) = x       ∷ xs y
```

Actually, my explanation above is a little bit of a lie. Often, the way I think
about dependently-typed programs has a lot to do with my intuition for "proofs"
and so on. But this leads you down the wrong path (and it's why writing a proof
that `cross-off` returns a list of the same length is the wrong move).

The actual termination checking algorithm is very simple, albeit strict: the
argument passed recursively must be *structurally* smaller. That's it.
Basically, the recursive argument has to be contained in one of the arguments
passed. It has nothing to do with Agda "seeing" inside the function `cross-off`
or anything like that. What we've done above (to make it terminate) is add
another argument to the function: the length of the vector. The argument is
implicit, but if we were to make it explicit in the recursive call:

```agda
sieve {suc n} (just x  ∷ xs) = suc x ∷ sieve {n} (cross-off x xs)
```
We can see that it does indeed get structurally smaller.

# Adding the Squaring Optimization

A simple improvement we should be able to make is stopping once we hit the
square root of the limit. Since we don't want to be squaring as we go, we'll use
the following identity:

$$(n + 1)^2 = n^2 + 2n + 1$$

to figure out the square of the next number from the previous. In fact, we'll
just pass in the limit, and reduce it by $2n + 1$ each time, until it reaches
zero:

```agda
primes : ∀ n → List (Fin n)
primes zero = []
primes (suc zero) = []
primes (suc (suc zero)) = []
primes (suc (suc (suc m))) = sieve 1 m (Vec.tabulate (just ∘ Fin.suc ∘ Fin.suc))
  where
  cross-off : ∀ {n} → ℕ → Vec (Maybe _) n → Vec (Maybe _) n

  sieve : ∀ {n} → ℕ → ℕ → Vec (Maybe (Fin (3 + m))) n → List (Fin (3 + m))
  sieve _ zero = List.mapMaybe id ∘ Vec.toList
  sieve _ (suc _) [] = []
  sieve i (suc l) (nothing ∷ xs) =     sieve (suc i) (l ∸ i ∸ i) xs
  sieve i (suc l) (just x  ∷ xs) = x ∷ sieve (suc i) (l ∸ i ∸ i) (cross-off i xs)

  cross-off p fs = Vec.foldr B f (const []) fs p
    where
      B = λ n → ℕ → Vec (Maybe (Fin (3 + m))) n

      f : ∀ {i} → Maybe (Fin (3 + m)) → B i → B (suc i)
      f _ xs zero    = nothing ∷ xs p
      f x xs (suc y) = x       ∷ xs y
```

# Finding Prime Factors

A slight variation on the code above (the first version) will give us the prime
factors of a number:

```agda
primeFactors : ∀ n → List (Fin n)
primeFactors zero = []
primeFactors (suc zero) = []
primeFactors (suc (suc zero)) = []
primeFactors (suc (suc (suc m))) = sieve (Vec.tabulate (just ∘ Fin.suc))
  where
  sieve : ∀ {n} → Vec (Maybe (Fin (2 + m))) n → List (Fin (3 + m))
  sieve [] = []
  sieve (nothing ∷ xs) = sieve xs
  sieve (just x  ∷ xs) = Vec.foldr B remove b xs sieve x
    where
    B = λ n → ∀ {i}
            → (Vec (Maybe (Fin (2 + m))) n
            → List (Fin (3 + m)))
            → Fin i
            → List (Fin (3 + m))

    b : B 0
    b k zero    = suc x ∷ k []
    b k (suc _) =         k []

    remove : ∀ {n} → Maybe (Fin (2 + m)) → B n → B (suc n)
    remove y ys k zero    = ys (k ∘ (nothing ∷_)) x
    remove y ys k (suc j) = ys (k ∘ (y ∷_)) j
```

Adding the squaring optimization complicates things significantly:

```agda
primeFactors : ∀ n → List (Fin n)
primeFactors zero = []
primeFactors (suc zero) = []
primeFactors (suc (suc zero)) = []
primeFactors (suc (suc (suc m))) = sqr (suc m) m suc sieve
  where
  _2F-_ : ∀ {n} → ℕ → Fin n → ℕ
  x           2F- zero = x
  zero        2F- suc y = zero
  suc zero    2F- suc y = zero
  suc (suc x) 2F- suc y = x 2F- y

  sqr : ∀ n
      → ℕ
      → (Fin n → Fin (2 + m))
      → (∀ {i} → Vec (Maybe (Fin (2 + m))) i → ℕ → List (Fin (3 + m)))
      → List (Fin (3 + m))
  sqr n       zero    f k = k [] n
  sqr zero    (suc l) f k = k [] zero
  sqr (suc n) (suc l) f k =
    let x = f zero
    in sqr n (l 2F- x) (f ∘ suc) (k ∘ (just x ∷_))

  sieve : ∀ {n} → Vec (Maybe (Fin (2 + m))) n → ℕ → List (Fin (3 + m))
  sieve xs′ i = go xs′
    where
    go : ∀ {n} → Vec (Maybe (Fin (2 + m))) n → List (Fin (3 + m))
    go [] = []
    go (nothing ∷ xs) = go xs
    go (just x  ∷ xs) = Vec.foldr B remove (b i) xs x go
      where
      B = λ n → ∀ {i}
              → Fin i
              → (Vec (Maybe (Fin (2 + m))) n → List (Fin (3 + m)))
              → List (Fin (3 + m))

      b : ℕ → B 0
      b zero    zero    k = suc x ∷ k []
      b zero    (suc y) k = k []
      b (suc n) zero    k = b n x k
      b (suc n) (suc y) k = b n y k

      remove : ∀ {n} → Maybe (Fin (2 + m)) → B n → B (suc n)
      remove y ys zero    k = ys x (k ∘ (nothing ∷_))
      remove y ys (suc j) k = ys j (k ∘ (y ∷_))
```

# Infinitude

The above sieve aren't "true" in that each `remove` is linear, so the
performance is $\mathcal{O}(n^2)$ overall. This is the same problem we ran into
with the naive infinite sieve in Haskell.

Since it bears such a similarity to the infinite sieve, we have to ask: can
*this* sieve be infinite? Agda supports a notion of infinite data, so it would
seem like it:

```agda
infixr 5 _◂_
record Stream (A : Set) : Set where
  constructor _◂_
  coinductive
  field
    head : A
    tail : Stream A
open Stream

primes : Stream ℕ
primes = sieve 1 nats
  where
  nats : Stream ℕ
  head nats = 0
  tail nats = nats

  sieve : ℕ → Stream ℕ → Stream ℕ
  head (sieve i xs) = suc i
  tail (sieve i xs) = remove i (head xs) (tail xs) (sieve ∘ suc ∘ (_+ i))
    where
    remove : ℕ → ℕ → Stream ℕ → (ℕ → Stream ℕ → Stream ℕ) → Stream ℕ
    remove zero zero zs       k = remove i (head zs) (tail zs) (k ∘ suc)
    remove zero (suc z) zs    k = remove i z zs (k ∘ suc)
    remove (suc y) zero zs    k = k zero (remove y (head zs) (tail zs) _◂_)
    remove (suc y) (suc z) zs k = remove y z zs (k ∘ suc)
```

But this won't pass the termination checker. What we actually need to prove to
do so is that there are infinitely many primes: [a nontrivial task in
Agda](https://gist.github.com/copumpkin/1286093).
