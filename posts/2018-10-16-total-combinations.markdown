---
title: Total Combinations
tags: Agda, Haskell
series: Total Combinatorics
---

Here's a quick puzzle: from a finite alphabet, produce an infinite list of
infinite strings, each of them unique.

It's not a super hard problem, but here are some examples of what you might get.
Given the alphabet of `0` and `1`, for instance, you could produce the
following:

```
0000000...
1000000...
0100000...
1100000...
0010000...
1010000...
0110000...
1110000...
0001000...
```

In other words, the enumeration of the binary numbers (least-significant-digit
first). We'll just deal with bits first:

```haskell
data Bit = O | I

instance Show Bit where
    showsPrec _ O = (:) '0'
    showsPrec _ I = (:) '1'
    showList xs s = foldr f s xs
      where
        f O a = '0' : a
        f I a = '1' : a
```

Thinking recursively, we can see that the tail of each list is actually the
original sequence, doubled-up:

<code class="sourceCode">
0<span class="er">000000</span>\... <br/>
1<span class="er">000000</span>\... <br/>
0<span class="er">100000</span>\... <br/>
1<span class="er">100000</span>\... <br/>
0<span class="er">010000</span>\... <br/>
1<span class="er">010000</span>\... <br/>
0<span class="er">110000</span>\... <br/>
1<span class="er">110000</span>\... <br/>
0<span class="er">001000</span>\... <br/>
</code>

As it happens, we get something like this pattern with the monad instance for
lists *anyway*:

```haskell
>>> (,) <$> [O,I] <*> "abc"
[(0,'a'),(0,'b'),(0,'c'),(1,'a'),(1,'b'),(1,'c')]
```

Well, actually it's the wrong way around. We want to loop through the *first*
list the quickest, incrementing the second slower. No worries, we can just use a
flipped version of `<*>`:

```haskell
infixl 4 <<>
(<<>) :: Applicative f => f (a -> b) -> f a -> f b
fs <<> xs = flip ($) <$> xs <*> fs

>>> (,) <$> [O,I] <<> "abc"
[(0,'a'),(1,'a'),(0,'b'),(1,'b'),(0,'c'),(1,'c')]
```

Brilliant! So we can write our function now, yes?

```haskell
bins = (:) <$> [O,I] <<> bins
```

Nope! That won't ever produce an answer, unfortunately. 

# Productivity

The issue with our definition above is that it's not lazy enough: it demands
information that it hasn't produced yet, so it gets caught in an infinite loop
before it can do anything!

We need to kick-start it a little, so it can produce output *before* it asks
itself for more. Because we know what the first line is going to be, we can just
tell it that:

```haskell
bins = (:) <$> [O,I] <<> (repeat O : tail bins)

>>> mapM_ print (take 8 (map (take 3) bins))
000
100
010
110
001
101
011
111
```

The property that this function has that the previous didn't is *productivity*:
the dual of termination. See, we want to avoid a *kind* of infinite loops in
`bins`, but we don't want to avoid infinite things altogether: the list it
produces is meant to be infinite, for goodness' sake. Instead, what it needs to
do is produce every new value in *finite* time.

# Checking Productivity

In total languages, like Agda, termination checking is a must. To express
computation like that above, though, you often also want a *productivity*
checker. Agda can do that, too.

Let's get started then. First, a stream:

```agda
infixr 5 _◂_
record Stream {a} (A : Set a) : Set a where
  coinductive
  constructor _◂_
  field
    head : A
    tail : Stream A
open Stream
```

In Agda, you can differentiate between infinite types (`coinductive` above),
finite types (you'd use the `inductive` keyword), and possibly finite types.
Also, this is a record, rather than a sum type: there's no empty case, so we
don't need multiple cases.

One of the interesting things about working with infinite data (when you're
forced to notice that it's infinite, as you are in Agda) is that *everything*
gets flipped. So you have to prove productivity, not totality; you use product
types, rather than sums; and to define functions, you use *co*patterns, rather
than patterns.

# Copatterns

Copatterns are a handy syntactic construct for writing functions about record
types. Let's start with an example, and then I'll try explain a little:

```agda
pure : ∀ {a} {A : Set a} → A → Stream A
head (pure x) = x
tail (pure x) = pure x
```

Here, we're defining `pure` on streams: `pure x` produces an infinite stream of
`x`. Its equivalent would be repeat in Haskell:

```haskell
repeat :: a -> [a]
repeat x = x : repeat x
```

Except instead of describing what it *is*, you describe how it *acts* (it's kind
of an intensional vs. extensional thing). In other words, if you want to make a
stream `xs`, you have to answer the questions "what's the head of `xs`?" and
"what's the tail of `xs`?"

Contrast this with pattern-matching: we're producing (rather than consuming) a
value, and in pattern matching, you have to answer a question for each *case*.
If you want to consume a list `xs`, you have to answer the questions "what do
you do when it's nil?" and "what do you do when it's cons?"

Anyway, I think the symmetry is kind of cool. Let's get back to writing our
functions.

# Sized Types

Unfortunately, we don't have enough to prove productivity yet. As an explanation
why, let's first try produce the famous `fibs` list. Written here in Haskell:

```haskell
fibs = 0 : 1 : zipWith (+) fibs (tail fibs)
```

Instead of `zipWith`, let's define `<*>`. That will let us use [idiom
brackets](https://agda.readthedocs.io/en/v2.5.4.1/language/syntactic-sugar.html#idiom-brackets).

```agda
_<*>_ : ∀ {a b} {A : Set a} {B : Set b}
      → Stream (A → B)
      → Stream A
      → Stream B
head (fs <*> xs) = head fs (head xs)
tail (fs <*> xs) = tail fs <*> tail xs
```

And here's `fibs`:

```agda
fibs : Stream ℕ
head fibs = 0
head (tail fibs) = 1
tail (tail fibs) = ⦇ fibs + tail fibs ⦈
```

But it doesn't pass the productivity checker! Because we use a higher-order
function (`<*>`), Agda won't look at how much it dips into the infinite supply
of values. This is a problem: we need it to know that `<*>` only needs the heads
of its arguments to produce a head, and so on. The solution? Encode this
information in the types.

```agda
infixr 5 _◂_
record Stream {i : Size} {a} (A : Set a) : Set a where
  coinductive
  constructor _◂_
  field
    head : A
    tail : ∀ {j : Size< i} → Stream {j} A
open Stream
```

Now, `Stream` has an implicit *size* parameter. Basically, `Stream {i} A` can
produce `i` more values. So `cons`, then, gives a stream one extra value to
produce:

```agda
cons : ∀ {i a} {A : Set a} → A → Stream {i} A → Stream {↑ i} A
head (cons x xs) = x
tail (cons x xs) = xs
```

Conversely, we can write a different definition of `tail` that consumes one
value[^tail]:

[^tail]: You might wonder why the definition of `tail` doesn't have this
    signature to begin with. The reason is that our record type must be
    *parameterized* (not indexed) over its size (as it's a record type), so we
    use a less-than proof instead.

```agda
tail′ : ∀ {i a} {A : Set a} → Stream {↑ i} A → Stream {i} A
tail′ {i} xs = tail xs {i}
```

For `<*>`, we want to show that its result can produce just as much values as
its inputs can:

```agda
_<*>_ : ∀ {i a b} {A : Set a} {B : Set b}
      → Stream {i} (A → B)
      → Stream {i} A
      → Stream {i} B
head (fs <*> xs) = head fs (head xs)
tail (fs <*> xs) = tail fs <*> tail xs
```

How does this help the termination/productivity checker? Well, for terminating
functions, we have to keep giving the `tail` field smaller and smaller sizes,
meaning that we'll eventually hit zero (and terminate). For productivity, we now
have a way to talk about "definedness" in types, so we can make sure that a
recursive call doesn't dip into a supply it hasn't produced yet.

One more thing: `Size` types have strange typing rules, mainly for ergonomic
purposes (this is why we're not just using an `ℕ` parameter). One of them is
that if you don't specify the size, it's defaulted to `∞`, so functions written
without size annotations don't have to be changed with this new definition:

```agda
pure : ∀ {a} {A : Set a} → A → Stream A
head (pure x) = x
tail (pure x) = pure x
```

Finally `fibs`:

```agda
fibs : ∀ {i} → Stream {i} ℕ
head fibs = 0
head (tail fibs) = 1
tail (tail fibs) = ⦇ fibs + tail fibs ⦈
```

# Bugs!

Before I show the Agda solution, I'd like to point out some bugs that were
revealed in the Haskell version by trying to implement it totally. First of all,
the function signature. "Takes an alphabet and produces unique strings" seems
like this:

```haskell
strings :: [a] -> [[a]]
```

But what should you produce in this case:

```haskell
strings []
```

So it must be a non-empty list, giving us the following type and definition:

```haskell
strings :: NonEmpty a -> [[a]]
strings (x :| xs) = (:) <$> (x:xs) <<> (repeat x : tail (strings (x :| xs)))
```

But this has a bug too! What happens if we pass in the following:

```haskell
strings (x :| [])
```

So this fails the specification: there is only one unique infinite string from
that alphabet (`pure x`). Interestingly, though, our implementation above also
won't produce any output beyond the first element. I suppose, in a way, these
things cancel each other out: our function does indeed produce all of the unique
strings, it's just a pity that it goes into an infinite loop to do so!

# Bringing it all Together

Finally, we have our function:

```agda
strings : ∀ {i a} {A : Set a} → A × A × List A → Stream {i} (Stream A)
head (strings (x , _ , _)) = pure x
tail (strings {A = A} xs@(x₁ , x₂ , xt)) = go x₂ xt (strings xs)
  where
  go : ∀ {i} → A → List A → Stream {i} (Stream A) → Stream {i} (Stream A)
  head (head (go y ys zs)) = y
  tail (head (go y ys zs)) = head zs
  tail (go _ [] zs) = go x₁ (x₂ ∷ xt) (tail zs)
  tail (go _ (y ∷ ys) zs) = go y ys zs
```

As you can see, we do need to kick-start it without a recursive call (the first
line is `pure x`). Then, `go` takes as a third argument the "tails" argument,
and does the kind of backwards Cartesian product we want. However, since we're
into the second element of the stream now, we want to avoid repeating what we
already said, which is why we have to give `go` `x₂`, rather than `x₁`. This is
what forces us to take at least two elements, rather than at least one, also: we
can't just take the tail of the call to `go` (this is what we did in the Haskell
version of `strings` with the `NonEmpty` list), as the recursive call to strings
then doesn't decrease in size:

```agda
strings : ∀ {i a} {A : Set a} → A × List A → Stream {i} (Stream A)
head (strings (x , _)) = pure x
tail (strings {A = A} xs@(x , xt)) = tail (go x xt (strings xs))
  where
  go : ∀ {i} → A → List A → Stream {i} (Stream A) → Stream {i} (Stream A)
  head (head (go y ys zs)) = y
  tail (head (go y ys zs)) = head zs
  tail (go _ [] zs) = go x xt (tail zs)
  tail (go _ (y ∷ ys) zs) = go y ys zs
```

Agda will warn about termination on this function. Now, if you slap a pragma on
it, it *will* produce the correct results for enough arguments, but give it one
and you'll get an infinite loop, just as you were warned!

# Further Work

I'm having a lot of fun with copatterns for various algorithms (especially
combinatorics). I'm planning on working on two particular tasks with them for
the next posts in this series:

Proving `strings`

: I'd like to prove that `strings` does indeed produce a stream of unique
  values. Following from that, it would be cool to do a Cantor diagonalisation
  on its output.
  
Permutations

: Haskell's
  [permutations implementation in
  Data.List](http://hackage.haskell.org/package/base-4.12.0.0/docs/src/Data.OldList.html#permutations)
  does some interesting tricks to make it as lazy as possible. It would be great
  to write an implementation that is verified to be as lazy as possible: the
  pattern of "definedness" is complex, though, so I don't know if it's possible
  with Agda's current sized types.
