---
title: Keeping Verification in Bounds
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

# Technique 3: Make Indices Correct-By-Construction

We're going to switch into Haskell now, and in particular to functional arrays.
These are data structures which aren't real arrays, but they offer you the kind
of interface you'd want from an array in a functional setting. You can't get
better than $\mathcal{O}(\log n)$ indexing, unfortunately
[@ben-amram_pointers_1992], but often it's enough.

The first "functional array" we're going to be looking at nested binary
random-access lists. It has $\mathcal{O}(\log n)$ indexing, as you might
expect, and amortized single-threaded $\mathcal{O}(1)$ `cons`.

It starts out like a binary random-access list ("random-access list" is
another name for "functional array"). You can find a full explanation of the
structure in your nearest copy of Purely Functional Data Structures
[@okasaki_purely_1999], but briefly: the structure mimics a binary number, in
that it's a list of "bits". At each set bit, it stores a tree with $2^i$
elements, where $i$ is the position in the list. In this way, every binary
number $n$ has an analogous list of "bits" which contains, in total, $n$
elements.

The "nested" part refers to how we're going to implement the trees. It works a
little like this:

```haskell
data Tree a = Leaf a | Node (Tree (a,a))
```

You might have to squint at that definition for a second to understand it:
instead of storing two trees at the `Node` constructor (which is what you'd
usually do), we store a tree with double the elements. This has two advantages:
all of the children have the same number of elements (this tree, for instance,
is always some power of 2), and it also cuts down on memory use.

For the binary random-access list, we'll use the nested encoding of trees to
encode the contents of each bit. There's an implementation of this very thing on
Hackage [@komuves_nested-sequence_2016], and Okasaki himself wrote something
very similar to it [-@okasaki_fast_1999], but we're going to go a little further
than both of those by indexing the type by its size. Here it is:

```haskell
data Bit = O | I

data Seq ns a where
    Nil  ::                      Seq '[]      a
    Even ::      Seq xs (a,a) -> Seq (O : xs) a
    Odd  :: a -> Seq xs (a,a) -> Seq (I : xs) a
```

The operations we're interested will be `cons` and `uncons`: for the indices,
they correspond to incrementing and decrementing the numbers, respectively. As
such, we'll need type-level functions for those:

```haskell
type family Inc (ns :: [Bit]) :: [Bit] where
    Inc '[] = '[I]
    Inc (O : xs) = I : xs
    Inc (I : xs) = O : Inc xs
```

And now the `cons` function:

```haskell
cons :: a -> Seq ns a -> Seq (Inc ns) a
cons x Nil        = Odd x Nil
cons x (Even  xs) = Odd x xs
cons x (Odd y ys) = Even (cons (x,y) ys)
```

However, we're going to run into trouble if we try to write `uncons`:

```haskell
type family Dec (ns :: [Bit]) :: [Bit] where
    Dec (I : xs) = O : xs
    Dec (O : xs) = I : Dec xs
    Dec '[] = ???
    
uncons :: Seq ns a -> (a, Seq (Dec ns) a)
uncons (Odd x xs) = (x, Even xs)
uncons (Even  xs) = case uncons xs of
    ((x,y),ys) -> (x, Odd y ys)
uncons Nil = ???
```

We *should* be able to write this function without returning a `Maybe`. Because
we statically know the size, we can encode "only nonempty sequences". The
problem is that `Seq [] a` isn't the only non-empty sequence: there's also `Seq
[O] a` and `Seq [O,O] a`, and so on. Our binary number system is redundant,
because it contains trailing zeroes.

We could add some kind of proof into the data structure, but that would (again)
be expensive. Instead, we can make the index *itself* correct-by-construction,
by choosing a non-redundant representation of binary numbers.

Here's the trick: instead of having a list of bits, we're going to have a list
of "the distance to the next one". This eliminates the redundancy, and
translates into our data structure like so:

```haskell
data N = Z | S N

data Nest n ns a where
    Odd  :: a -> (Seq    ns (a,a)) -> Nest Z     ns a
    Even ::      (Nest n ns (a,a)) -> Nest (S n) ns a

data Seq ns a where
    Nil  :: Seq '[] a
    Cons :: Nest n ns a -> Seq (n : ns) a
```

Lovely! The other benefit of this is that the original *also* contained
redundancy, whereas this doesn't. And, crucially for our `uncons`, we now know
that any non-empty list of bits is a non-zero list of bits, so we can type
"nonempty sequence" easily:

```haskell
type family Dec (n :: N) (ns :: [N]) = (r :: [N]) | r -> n ns where
    Dec (S n) ns       = Z : Dec n ns
    Dec Z     '[]      = '[]
    Dec Z     (n : ns) = S n : ns

uncons :: Seq (n : ns) a -> (a, Seq (Dec n ns) a)
uncons (Cons xs') = go xs'
  where
    go :: Nest n ns a -> (a, Seq (Dec n ns) a)
    go (Odd x Nil) = (x, Nil)
    go (Odd x (Cons xs)) = (x, Cons (Even xs))
    go (Even xs) = case go xs of ((x,y),ys) -> (x, Cons (Odd y ys))
```

We're still not done, though: here's our new type family for incrementing
things.

```haskell
type family Inc (ns :: [N]) :: [N] where
    Inc '[] = '[Z]
    Inc (S n : ns) = Z : n : ns
    Inc (Z   : ns) = Carry (Inc ns)
    
type family Carry (ns :: [N]) :: [N] where
    Carry '[] = '[]
    Carry (n : ns) = S n : ns
```

The `Carry` there is ugly, and that ugliness carries into the `cons` function:

```haskell
cons :: a -> Seq ns a -> Seq (Inc ns) a
cons x Nil = Cons (Odd x Nil)
cons x' (Cons xs') = go x' xs'
  where
    go :: a -> Nest n ns a -> Seq (Inc (n:ns)) a
    go x (Even  xs) = Cons (Odd x (Cons xs))
    go x (Odd y Nil) = Cons (Even (Odd (x,y) Nil))
    go x (Odd y (Cons ys)) = carry (go (x,y) ys)

    carry :: Seq ns (a,a) -> Seq (Carry ns) a
    carry Nil = Nil
    carry (Cons xs) = Cons (Even xs)
```

To clean it up, we're going to use another technique.

# Technique 4: Provide Information on Indices as Early as Possible

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

Looking back at our definition of `Inc`, we can actually provide more
information a little sooner:

```haskell
type family Inc (ns :: [N]) :: [N] where
    Inc '[] = '[Z]
    Inc (S n : ns) = Z : n : ns
    Inc (Z   : ns) = Carry (Inc ns)
```

In all of the outputs, the list is non-empty. We can encode that, by having two
different functions for the head and tail of the list:

```haskell
type family IncHead (ns :: [N]) :: N where
    IncHead '[] = Z
    IncHead (n : ns) = IncHead' n ns

type family IncHead' (n :: N) (ns :: [N]) :: N where
    IncHead' (S n) ns = Z
    IncHead' Z ns = S (IncHead ns)

type family IncTail (ns :: [N]) :: [N] where
    IncTail '[] = '[]
    IncTail (n : ns) = IncTail' n ns

type family IncTail' (n :: N) (ns :: [N]) :: [N] where
    IncTail' (S n) ns = n : ns
    IncTail' Z ns = IncTail ns

type Inc (ns :: [N]) = IncHead ns : IncTail ns
```

This tells the typechecker that we're not returning an empty sequence right
away, so we don't have to pattern-match to prove it later, giving us a more
efficient function.

```haskell
cons :: a -> Seq ns a -> Seq (Inc ns) a
cons x' xs' = Cons (go x' xs')
  where
    go :: a -> Seq ns a -> Nest (IncHead ns) (IncTail ns) a
    go x Nil = Odd x Nil
    go x (Cons (Even  xs)) = Odd x (Cons xs)
    go x (Cons (Odd y ys)) = Even (go (x,y) ys)
```

# Technique 5: Lazy Proofs

Briefly after introducing the binary random-access list, Okasaki describes the
*skew-binary* random-access list. As well as having the same indexing cost as
the type above, it supports $\mathcal{O}(1)$ `cons`. But wait---didn't the
previous structure have $\mathcal{O}(1)$ `cons`? Not really. Unfortunately, in a
pure functional setting, imperative-style amortization measurements aren't
always valid. Say we perform a `cons` in the worst case, and it takes $\log n$
time. In an imperative setting, that's no problem, because all of the rest of
the operations are not going to be on the worst-case. In a pure setting, though,
the old structure is still sitting around. You can still access it, and you can
still get that awful worst-case time.

This is where the skew binary tree comes in. It's based on the [skew binary
numbers](https://en.wikipedia.org/wiki/Skew_binary_number_system): these work
similarly to binary, but you're allowed have (at most) a single 2 digit before
any ones. This gives you $\mathcal{O}(1)$ incrementing and decrementing, which
is what we need here. Let's get started.

First, our type-level numbers. We're going to use the sparse encoding as above,
but we need some way to encode "you're only allowed one 2". The most lightweight
way to do it I can think of is by implicitly assuming the second number in the
list of gaps is one less than the others. In other words, we encode a 2 with
`[n, 0, m]`. That `0` means that at position `n` there's a 2, not a 1.

The corresponding type families for increment and decrement are clearly
$\mathcal{O}(1)$:

```haskell
type family Inc (ns :: [N]) = (ms :: [N]) | ms -> ns where
    Inc '[]              = Z   : '[]
    Inc (x  : '[])       = Z   : x  : '[]
    Inc (x  : Z    : xs) = S x : xs
    Inc (x1 : S x2 : xs) = Z   : x1 : x2 : xs

type family Dec (n :: N) (ns :: [N]) = (ms :: [N]) | ms -> n ns where
    Dec (S x)  xs            = x  : Z : xs
    Dec Z     '[]            = '[]
    Dec Z     (x  : '[])     = x  : '[]
    Dec Z     (x1 : x2 : xs) = x1 : S x2 : xs
```

We don't need to split this into head and tail families as we did before because
there's no recursive call: we know all we're ever going to know about the output
following *any* match on the input.

There's another problem before we write the implementation: we can't use the
`Nest` construction that we had before, because then the head would be buried in
$\log n$ constructors (or thereabouts). Instead, we're going to have to use
GADTs to encode the "gap" type, alongside the relevant tree. This gap type is
going to be very similar to the $\geq$ proof we had for the modular counters,
but with an extra parameter:

```haskell
data Gap (n :: N) (g :: N) (m :: N) where
    Zy :: Gap n Z n
    Sy :: Gap n g m -> Gap n (S g) (S m)
```

`Gap n g m` means there is a gap of `g` between `n` and `m`. Or, stated another
way, it means `n + g = m`. Its inductive structure mimics the `g` parameter
(it's basically the `g` parameter itself with some added information).

With all of that together, here's the definition of the array itself:

```haskell
type family Tree (n :: N) (a :: Type) where
    Tree Z a = a
    Tree (S n) a = Node n a

data Node n a = Node a (Tree n a) (Tree n a)

data SeqTail (n :: N) (ns :: [N]) (a :: Type) where
    NilT  :: SeqTail n '[] a
    ConsT :: Gap n g m
          -> Tree m a
          -> SeqTail (S m) ms a
          -> SeqTail n (g : ms) a

data Seq (ns :: [N]) (a :: Type) where
    Nil  :: Seq '[] a
    Cons :: Gap Z g n
         -> Tree n a
         -> SeqTail n ns a
         -> Seq (g : ns) a
```

The `cons` operation again mimics the increment function, but there's one final
snag before it'll typecheck:

```haskell
cons :: a -> Seq ns a -> Seq (Inc ns) a
cons x Nil = Cons Zy x NilT
cons x (Cons zn y NilT) = Cons Zy x (ConsT zn y NilT)
cons x (Cons zn y1 (ConsT Zy y2 ys)) = Cons(Sy zn) (Node x y1 y2) ys
cons x (Cons zn y1 (ConsT (Sy nm) y2 ys)) =
    Cons Zy x (ConsT zn y1 (ConsT ??? y2 ys))
```

On the final line, the `???` is missing. In the unverified version, `nm` would
slot right in there. Here, though, if we try it we get an error, which basically
amounts to:

```haskell
Gap n g m /= Gap (S n) g (S m)
```

At this point, I'd usually throw out the inductive-style proof, and replace it
with a proof of equality, which I'd aggressively erase in all of the functions.
I said at the beginning I wouldn't cheat, though, so here's what I'll do
instead:

```haskell
gapr :: Gap n g m -> Gap (S n) g (S m)
gapr Zy       = Zy
gapr (Sy pnm) = Sy (gapr pnm)

cons :: a -> Seq ns a -> Seq (Inc ns) a
cons x Nil = Cons Zy x NilT
cons x (Cons zn y NilT) = Cons Zy x (ConsT zn y NilT)
cons x (Cons zn y1 (ConsT Zy y2 ys)) = Cons (Sy zn) (Node x y1 y2) ys
cons x (Cons zn y1 (ConsT (Sy nm) y2 ys)) =
    Cons Zy x (ConsT zn y1 (ConsT (gapr nm) y2 ys))
```

At first glance, we've lost the complexity bounds. That `gapr` operation is
$\log n$ (or something), and we're performing it pretty frequently. We might
keep the amortized bounds, but isn't that not really worthy in a pure setting?

That would all be true, if it weren't for laziness. I haven't fully worked out
the various proofs here yet, but `cons` distributes the work for `gapr` among
the rest of the structure, only demanding it when it's called for. In this way,
we get back the amortized bounds: in contrast to destructive updates, work done
by evaluating a thunk *is* shared in a pure language, so you really do only pay
for the worst-case once.

We could eliminate the amortization with scheduling here, I think. I may return
to it in the future.

# Technique 6: When All Else Fails, Prove it Later

About a year ago, I
[tried](/posts/2017-04-23-verifying-data-structures-in-haskell-lhs.html) to
write a verified version of binomial heaps, which could then be used for sorting
traversable containers. Unfortunately, I couldn't figure out how to write
delete-min, and gave up. I *did* recognize that the redundancy of the
binary representation was a problem, but I couldn't figure out much more than
that.

Now, though, we have a new non-redundant representation of binary numbers, and
some handy techniques to go along with it.

Unfortunately, I ran into a similar roadblock in the implementation. Here's the
point where I was stuck:

```haskell
data Zipper a n xs = Zipper a (Node n a) (Binomial n xs a)

slideLeft :: Zipper a (S n) xs -> Zipper a n (Z : xs)
slideLeft (Zipper m (t :< ts) hs) = Zipper m ts (Cons (Odd t hs))

minView :: Ord a => Binomial n (x : xs) a -> (a, Binomial n (Decr x xs) a)
minView (Cons xs') = unZipper (go xs')
  where
    unZipper (Zipper x _ xs) = (x, xs)

    go :: forall a n x xs. Ord a => Nest n x xs a -> Zipper a n (Decr x xs)
    go (Even xs) = slideLeft (go xs)
    go (Odd (Root x ts) Empty) = Zipper x ts Empty
    go (Odd c@(Root x ts) (Cons xs)) =
        case go xs of
            (Zipper m (t' :< _) hs)
              | m >= x -> Zipper x ts (Cons (Even xs))
              | otherwise ->
                  Zipper m ts
                      (case hs of
                           Empty -> Cons (Even (Odd (mergeTree c t') Empty))
                           Cons hs' -> Cons (Even (carryOneNest (mergeTree c t') hs')))
```

The last two lines don't typecheck! The errors were complex, but effectively
they stated:

> `Could not deduce` 
>
> > `x : xs ~ [Z]`{.haskell}
>
> `from the context`
>
> > `Decr x xs ~ []`{.haskell}

and:

> `Could not deduce` 
>
> > `x : xs ~ Inc (y : ys)`{.haskell}
>
> `from the context`
>
> > `Decr x xs ~ y : ys`{.haskell}

The thing is, all of those look pretty provable. So, for this technique, we
first write in the proofs we need, and *assume* we have them. This means
changing `minView` to the following:

```haskell
data Zipper a n xs = Zipper a (Node n a) (Binomial n xs a)

slideLeft :: Zipper a (S n) xs -> Zipper a n (Z : xs)
slideLeft (Zipper m (t :< ts) hs) = Zipper m ts (Cons (Odd t hs))

minView :: Ord a => Binomial n (x : xs) a -> (a, Binomial n (Decr x xs) a)
minView (Cons xs') = unZipper (go xs')
  where
    unZipper (Zipper x _ xs) = (x, xs)

    go :: forall a n x xs. Ord a => Nest n x xs a -> Zipper a n (Decr x xs)
    go (Even xs) = slideLeft (go xs)
    go (Odd (Root x ts) Empty) = Zipper x ts Empty
    go (Odd c@(Root x ts) (Cons xs)) =
        case go xs of
            (Zipper m (t' :< _) (hs :: Binomial (S n) (Decr y ys) a))
              | m >= x -> Zipper x ts (Cons (Even xs))
              | otherwise ->
                  Zipper m ts
                      (case hs of
                           Empty -> gcastWith (lemma1 @y @ys Refl)
                               Cons (Even (Odd (mergeTree c t') Empty))
                           Cons hs' -> gcastWith (lemma2 @y @ys Refl)
                               Cons (Even (carryOneNest (mergeTree c t') hs')))
```

And writing in the templates for our lemmas:

```haskell
lemma1 :: forall x xs. Decr x xs :~: '[] -> x : xs :~: Z : '[]
lemma1 = _

lemma2 :: forall x xs y ys. Decr x xs :~: y : ys -> x : xs :~: Inc (y : ys)
lemma2 = _
```

We now need to provide the *implementations* for `lemma1` and `lemma2`. With
this approach, even if we fail to do the next steps, we can cop out here and sub
in `unsafeCoerce Refl` in place of the two proofs, maintaining the efficiency.
We won't need to, though! 

The next step is to look for things in the surrounding area which could act like
singletons for the lemmas. They'll need to do pattern matching, and the types
won't be around at runtime, so we'll need some structure which we can pattern
match on which will tell us about the types. 

It turns out that the `xs` and `hs'` floating around can do exactly that: they
tell us about the type-level `y` and `x`. So we just pass them to the lemmas
(where they're needed). This changes the last 2 lines of `minView` to:

```haskell
Empty -> gcastWith (lemma1 Refl xs) Cons (Even (Odd (mergeTree c t') Empty))
Cons hs' -> gcastWith (lemma2 Refl xs hs') Cons (Even (carryOneNest (mergeTree c t') hs'))
```

Now, we just have to fill in the lemmas! If we were lucky, they'd actually be
constant-time.

```haskell
lemma1 :: forall x xs n a. Decr x xs :~: '[]
       ->  Nest n x xs a
       -> x : xs :~: Z : '[]
lemma1 Refl (Odd _ Empty) = Refl

lemma2 :: forall x xs y ys n a.
          Decr x xs :~: y : ys
       -> Nest n x xs a
       -> Nest n y ys a
       -> x : xs :~: Inc (y : ys)
lemma2 Refl (Even (Odd _ Empty)) (Odd _ Empty) = Refl
lemma2 Refl (Odd _ (Cons _)) (Even _) = Refl
lemma2 Refl (Even xs) (Odd _ (Cons ys)) =
  gcastWith (lemma2 Refl xs ys) Refl
```

If they *had* been constant-time, that would have let us throw them out: each
proof would essentially show you what cases needed to be scrutinized to satisfy
the typechecker. You then just scrutinize those cases in the actual function,
and it should all typecheck.

As it is, `lemma2` is actually ok. It does cost $\mathcal{O}(\log n)$, but so
does `carryOneNest`: we've maintained the complexity! We *could* stop here,
satisfied.

There's another option, though, one that I picked up from Stephanie Weirich's
talk [-@weirich_dependent_2017]: you thread the requirement through the
function as an equality constraint. It won't always work, but when your
function's call tree matches that of the proof, the constraint will indeed be
satisfied, with no runtime cost. In this case, we can whittle down the proof
obligation to the following:

```haskell
Inc (Decr x xs) ~ (x : xs)
```

Now we change the recursive `go` into continuation-passing style, and add that
constraint to its signature, and everything works!

```haskell
minView :: Ord a => Binomial n (x : xs) a -> (a, Binomial n (Decr x xs) a)
minView (Cons xs') = go xs' \(Zipper x _ xs) -> (x,xs)
  where
    go :: Ord a
       => Nest n x xs a
       -> (Inc (Decr x xs) ~ (x : xs) => Zipper a n (Decr x xs) -> b) -> b
    go (Even xs) k = go xs \(Zipper m (t :< ts) hs) -> k (Zipper m ts (Cons (Odd t hs)))
    go (Odd (Root x ts) Empty) k = k (Zipper x ts Empty)
    go (Odd c@(Root x cs) (Cons xs)) k =
        go xs
            \case
                Zipper m _ _ | m >= x ->
                    k (Zipper x cs (Cons (Even xs)))
                Zipper m (t :< ts) Empty ->
                    k (Zipper m ts (Cons (Even (Odd (mergeTree c t) Empty))))
                Zipper m (t :< ts) (Cons hs) ->
                    k (Zipper m ts (Cons (Even (carryOneNest (mergeTree c t) hs))))
```

# Conclusion

As I mentioned in the beginning, a huge amount of this stuff is *much* easier
using other systems. On top of that, there's currently a lot of work being done
on dependent type erasure, so that proofs like the above don't even exist at
runtime. In other words, there's a chance that all of these techniques will soon
be useless!

Efficient proof-carrying code makes for an interesting puzzle, though, even if
it is a bit of a hair shirt.



# References
 
