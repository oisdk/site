---
title: Fast Verified Data Structures
tags: Haskell, Agda
bibliography: Agda.bib
---

One of the favorite pastimes of both Haskell and Agda programmers alike is
verifying data structures. Among those verified are Red-Black trees
[@might_missing_2015; @weirich_depending_2014, verified for balance], perfect
binary trees [@hinze_perfect_1999], square matrices [@okasaki_fast_1999], search
trees [@mcbride_how_2014, verified for balance and order], and binomial heaps
[@hinze_numerical_1998, verified for structure].

There are many ways to verify data structures. One technique which has had
recent massive success is to convert Haskell code to Coq, and then verify the
Coq translation: this was the route taken by @breitner_ready_2018-1 to verify
`Set` and `IntSet` in containers (a mammoth achievement, in my opinion).

This approach has some obvious advantages: you separate implementation from
testing (which is usually a good idea), and your verification language can be
different from your implementation language, with each tailored towards its
particular domain.

LiquidHaskell [@bakst_liquidhaskell_2018] (and other tools like it) adds an
extra type system to Haskell tailor-made for verification. The added type system
(refinement types) is more automated (the typechecker uses Z3), more suited for
"invariant"-like things (it supports subtyping), and has a bunch of
domain-specific built-ins (reasoning about sets, equations, etc.). I'd encourage
anyone who hasn't used it to give it a try: especially if you're experienced
writing any kind of proof in a language like Agda or Idris, LiquidHaskell proofs
are *shockingly* simple and easy: it can make verification a joy.

What I'm going to focus on today, though, is writing *correct-by-construction*
data structures, using Haskell and Agda's own type systems. In particular, I'm
going to look at how to write *fast* verification. In the other two approaches,
we don't really care about the "speed" of the proofs: sure, it's nice to speed
up compilation and so on, but we don't have to worry about our implementation
suffering at runtime because of some complex proof. When writing
correct-by-construction code, though, our task is doubly hard: we now have to
worry about the time complexity of both the implementation *and the proofs*.

In this post, I'm going to demonstrate some techniques to write proofs that
stay within the complexity bounds of the algorithms they're verifying (without
cheating!). Along the way I'm going to verify some data structures I haven't
seen verified before.

# Technique 1: Start With an Unverified Implementation, then Index

To demonstrate the first two techniques, we're going to write a type for modular
arithmetic. For a more tactile metaphor, think of the flip clock:

![](https://upload.wikimedia.org/wikipedia/commons/c/c3/Split-flap_display.jpg)

Each digit can be incremented $n$ times, where $n$ is whatever base you're using
(12 for our flip-clock above). Once you hit the limit, it flips the next digit
along. We'll start with just one digit, and then just string them together to
get our full type. That in mind, our "digit" type has two requirements:

#. It should be incrementable.
#. Once it hits its limit, it should flip back to zero, and let us know that a
flip was performed.

Anyone who's used a little Agda or Idris will be familiar with the `Fin` type:

```agda
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)
```

`Fin n` is the standard way to encode "numbers smaller than `n`". However, for
digits they're entirely unsuitable: since the limit parameter changes on
successor, the kind of increment we want is $\mathcal{O}(n)$:

```agda
try-suc : ∀ {n} → Fin n → Maybe (Fin n)
try-suc (suc x) = Maybe.map suc (try-suc x)
try-suc {suc n} zero with n
... | zero = nothing
... | suc _ = just (suc zero)

suc-flip : ∀ {n} → Fin n → Fin n × Bool
suc-flip {suc n} x = maybe (_, false) (zero , true) (try-suc x)
suc-flip {zero} ()
```

If we keep going down this path with proofs in mind, we might next look at the
various $\leq$ proofs in the Agda standard library
([here](https://github.com/agda/agda-stdlib/blob/18b45b151f44cee2114fa4b3c1ad9ea532baf919/src/Data/Nat/Base.agda#L28),
[here](https://github.com/agda/agda-stdlib/blob/18b45b151f44cee2114fa4b3c1ad9ea532baf919/src/Data/Nat/Base.agda#L117),
and
[here](https://github.com/agda/agda-stdlib/blob/18b45b151f44cee2114fa4b3c1ad9ea532baf919/src/Data/Nat/Base.agda#L133)),
and see if we can we can wrangle them into doing what we want.

For me, though, this wasn't a fruitful approach. Instead, we'll try and think of
how we'd do this without proving anything, and then see if there's any place in
the resulting data structure we can hang some proof.

So, in an unproven way, let's start with some numbers. Since we're going to be
incrementing, they'd better be unary:

```agda
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
```

And then, for the "flippable" type, we'll just store the limit alongside the
value:

```agda
record Flipper : Set where
  constructor _&_
  field
    val : ℕ
    lim : ℕ
```

We're not there yet: to check if we've gone over the limit, we'll still have to
compare `val` and `lim`. Hopefully you can guess the optimization we'll make:
instead of storing the limit, we'll store the space left:

```agda
record Flipper : Set where
  constructor _&_
  field
    space : ℕ
    val   : ℕ
```

And we get our flip function:

```agda
suc-flip : Flipper → Flipper × Bool
suc-flip (zero  & n) = (suc n & zero ), true
suc-flip (suc m & n) = (m     & suc n), false
```

When there's no space left, the digit must be maximal (9 in decimal, for
instance), so it'll be one less than the base. That lets us stick it in for the
base, rather than recalculating. In the other case, we just take one from the
space left, and add it to the value.

So, to "prove" this implementation, we might first reach for an equality proof
that `val + space` is equal to your base. Don't! Both `val` and `space` are
inductive structures, which could be giving us information on every application
of `suc`! Let's set our sights on `val` and see how we can hang our proofs off
of it.

We're going to upgrade our Peano number with some information, which means that
our resulting type is going to look an awful lot like a Peano number. In other
words, two cases: `zero` and `suc`.

```agda
data Val _ : Set where
  zero-case : Val _
  suc-case  : Val _ → Val _
```

For the `suc-case`, remember we only want to be allowed to increment it when the
space left is more than zero. So let's encode it:

```agda
data Val _ : ℕ → Set where
  zero-case : Val _
  suc-case  : ∀ {space} → Val _ (suc space) → Val _ space
```

And for the `zero-case`, the space left is just the base. So let's stick the
base into the type as well:

```agda
data Val (base : ℕ) : ℕ → Set where
  zero-case : Val base base
  suc-case  : ∀ {space} → Val base (suc space) → Val base space
```

(We've changed around the way "base" works: it's now one smaller. So to encode
base-10 you'd have `Val 9 space`. You can get back to the other encoding with a
simple wrapper, this way just makes things slightly easier from now on).

Finally, our flipper:

```agda
record Flipper (base : ℕ) : Set where
  constructor _&_
  field
    space : ℕ
    val : Val base space

suc-flip : ∀ {n} → Flipper n → Flipper n × Bool
suc-flip (zero  & m) = (_ &  zero-case) , true
suc-flip (suc n & m) = (n & suc-case m) , false
```

Great! Everything works.

You may have noticed that the `Val` type is actually a proof for $\geq$ in
disguise:

```agda
data _≥_ (m : ℕ) : ℕ → Set where
  m≥m : m ≥ m
  m≥p : ∀ {n} → m ≥ suc n → m ≥ n
```

And the flipper itself is just an existential in disguise:

```agda
Flipper : ℕ → Set
Flipper n = ∃ (n ≥_)

suc-flip : ∀ {n} → Flipper n → Flipper n × Bool
suc-flip (zero  , m) = (_ , m≥m  ), true
suc-flip (suc n , m) = (n , m≥p m), false
```

Hopefully this explanation will help you understand how to get from the
specification to those 8 lines. This technique is going to come in especially
handy later when we base data structures off of number systems.

# Technique 2: Once you eliminate the impossible, whatever remains, no matter how improbable, must be the truth.

Sometimes, we don't have the luxury of redefining the datatype we want to
verify. Say we want to add an operation to an already-existing type, for
instance. Here, we want to add two in one go: inversion, and conversion from a
natural number.

Inversion is where we would swap around the `space` and `val` in the unverified
version. Since `space` is stored as a natural number, though, inversion can be
defined in terms of it. Let's give it a go then.

```agda
fromNat : ∀ {m} (n : ℕ) → Mod m
fromNat zero    = _ , m≥m
fromNat (suc n) = ??? (fromNat n)
```

The problem we run into is that our successor function doesn't know that there's
space left. So we'd have to run the "flipping" version, which I don't want to do.

So what do we do instead? We *assume* there's space left:

```agda
fromNat : ∀ {m} (n : ℕ) → Mod m
fromNat zero    = _ , m≥m
fromNat (suc n) with fromNat n
... | suc space , n-1 = space , m≥p n-1
... | zero      , n-1 = ???
```

Now, all we have to do is prove that the second case is impossible.

In contrast to proving the "happy path" is correct, this technique lets us carry
out expensive proofs of the unhappy path *without* paying for them. Why? Because
they'll never be executed! We can take as much time as we want in the unhappy
path because we *know* that it won't exist at runtime.

For the full function, we'll need to pass in `m ≥ n`, but it can be marked
irrelevant, so we again don't have to pay for it.

<details>
<summary>
`fromNat` implementation
</summary>
```agda
toNat : ∀ {n m} → n ≥ m → ℕ
toNat m≥m = zero
toNat (m≥p n≥m) = suc (toNat n≥m)

fromNat-≡ : ∀ {n} m → .(n≥m : n ≥ m) →  Σ[ n-m ∈ Mod n ] toNat (proj₂ n-m) ≡ m
fromNat-≡ zero n≥m = (-, m≥m) , refl
fromNat-≡ (suc m) n≥m with fromNat-≡ m (m≥p n≥m)
... | (suc s , p  ) , x≡m  = (s , m≥p p), cong suc x≡m
... | (zero  , n≥0) , refl = Irrel.⊥-elim (contra _ zero n≥0 n≥m)
  where
  import Data.Nat.Properties as Prop

  n≱sk+n : ∀ n k {sk+n} → sk+n ≡ suc k ℕ.+ n → n ≥ sk+n → ⊥
  n≱sk+n n k wit (m≥p n≥sk+n) = n≱sk+n n (suc k) (cong suc wit) n≥sk+n
  n≱sk+n n k wit m≥m with Prop.+-cancelʳ-≡ 0 (suc k) wit
  ... | ()

  contra : ∀ n m → (n≥m : n ≥ m) → n ≥ suc (m ℕ.+ toNat n≥m) → ⊥
  contra n m m≥m n≥st = n≱sk+n n zero (cong suc (Prop.+-comm n 0)) n≥st
  contra n m (m≥p n≥m) n≥st = contra n (suc m) n≥m (subst (λ x → n ≥ suc x) (Prop.+-suc m (toNat n≥m)) n≥st)

fromNat : ∀ {n} m → .(n≥m : n ≥ m) → Mod n
fromNat m n≥m = proj₁ (fromNat-≡ m n≥m)
```
</details>

# Technique 3: Provide Information on Indices as Early as Possible

You occasionally see people wonder about the usual definition of addition on
Peano numbers:

```agda
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
```

It's very simple, with only two equations. When someone sees the following
error, then:

```agda
couldn't match type n with n + 0
```

They might be tempted to add it as an equation to the function:

```agda
_+_ : ℕ → ℕ → ℕ
zero  + m    = m
n     + zero = n
suc n + m    = suc (n + m)
```

Similarly, when someone sees the other error commonly found with $+$:

```agda
couldn't match type S n + m with n + S m
```

They'll add that equation in too! In fact, that particular equation will provide
a valid definition of $+$:

```agda
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = n + suc m
```

So why is the first definition of + the one almost always used? Because it
*maximizes output information from minimal input*. Take the second
implementation above, the one with the zero on the right. In this function, we
have to look at the second argument in the second clause: in other words, we
don't get to find out about the output until we've looked at both `n` and `m`.
In the usual definition, if you know the first argument is `suc` something, you
also know the *output* must be `suc` something.

Similarly with the third implementation: we have to examine the first argument
in its *entirety* before we wrap the output in a constructor. Yes, we can of
course prove that they're all equivalent, but remember: proofs are expensive,
and we're looking for speed here. So the first definition of $+$ is our best
bet, since it tells us the most without having to prove anything.

# References
