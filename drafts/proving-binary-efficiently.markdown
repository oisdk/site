---
title: Proving Binary Numbers Efficiently
tags: Agda
series: Binary Numbers
bibliography: Agda.bib
---

Last time, we saw an implementation of binary numbers that had $\mathcal{O}(1)$
increment and decrement, as well as the usual $\mathcal{O}(\log_2 n)$ and
$\mathcal{O}((\log_2 n)^2)$ times for addition and multiplication, respectively.

Since then, there's been some exciting news: @harvey_integer_2019 have
discovered a $\mathcal{O}(n \log_2 n)$ algorithm for integer multiplication.
Before you go comparing that to the bounds I stated for my implementations, I
should point out that this $n$ refers to the number of bits---*not* the size of
the numbers themselves.
In other words, this algorithm represents an improvement from $\mathcal{O}(n^2)$
to $\mathcal{O}(n \log_2 n)$.

However, despite this massive improvement, I won't be making use of the new
algorithm.
What's more, I must confess that this isn't even the first integer
multiplication algorithm with better
big-$\mathcal{O}$ that I've ignored: the [Karatsuba
algorithm](https://en.wikipedia.org/wiki/Karatsuba_algorithm), for instance, was
discovered in the 60s, and it isn't even that complex to implement!

What's going on? Why am I wilfully using substandard algorithms? John Carlos
Baez illustrated the problem pretty well in a tweet:

> WOW!  A new paper claims to have found a more efficient algorithm for
> multiplying large numbers.  It supposedly runs in $\mathcal{O}(n \log n)$ time - this had
> never been achieved before.  One catch: it only works on numbers with at least
> this many digits:
>
> (cont) 
> 
> `
> 1044388881413152506691752710716624382579964249047383780384233483283953907971557456848
> 8268119349975583408901067144392628379875734381839539079715574568488268119349975583408
> 9010671443926283798757343818579360726323608785136527794595697654370999834036159013438
> 3718314428070011855946226376318839397712745672334684344586617496807908705803704071284
> 0487401186091144679777835980290066869389768817877859469056301902609405995794534328234
> 6930302669644305902501597239986771421554169383555988529148631823791443449673408781187
> 2639496475100189041349008417061675093668333850551032972088269550769983616369411933015
> 2137968258371880918336567512213184928463681255502259983004123447848625956744921946170
> 2380650591324561082573183538008760862210283427019769820231316901767800667519548507992
> 1636419370285375124784014907159135459982790513399611551794271106831134090584272884279
> 7915548497829543235345170652232690613949059876930021229633956877828789484406160074129
> 4567491982305057164237715481632138063104590291613692670834285644073044789997190178146
> 5763473223850267253059899795996090799469201774624817718449867455659250178329070473119
> 4331655508075682218465717463732968849128195203174570024409266169108741483850784119298
> 0452298185733897764810312608590300130241346718972667321649151113160292078173803343609
> 0243804708340403154190336`
> 
> ---John Carlos Baez (\@johncarlosbaez)
> [March 27, 2019](https://twitter.com/johncarlosbaez/status/1110736531671539713)

The Karatsuba algorithm is similar: it only becomes faster than the naive method
at around 300 bits, far more than I'm likely to see in my applications.

So we're not interested in these algorithms because, though their
big-$\mathcal{O}$ is certainly better, their actual performance (for my use
case) is not necessarily so. As it turns out, the constant-time increment that I
went to so much trouble to achieve suffers similarly!
After some benchmarking, it turned out to be slower than the one in Binary-4
(from Sergei @meshveliani_binary-4_2018).
After some more benchmarking, I settled on the following implementation, which
was tied for fastest:

```agda
infixr 5 I∷_ O∷_ 0<_
data 𝔹⁺ : Set where
  1ᵇ : 𝔹⁺
  I∷_ : 𝔹⁺ → 𝔹⁺
  O∷_ : 𝔹⁺ → 𝔹⁺

data 𝔹 : Set where
  0ᵇ : 𝔹
  0<_ : 𝔹⁺ → 𝔹
```

# Decomposition and Call-Pattern Specialisation

One of the most useful techniques for making it easier to prove things about
dependently-typed code is *decomposition*. To explain it, let's look at an
implementation of the increment function on the type above:

```agda
inc : 𝔹 → 𝔹
inc 0ᵇ = 0< 1ᵇ
inc (0< 1ᵇ) = 0< O∷ 1ᵇ
inc (0< O∷ xs) = 0< I∷ xs
inc (0< I∷ xs) = case inc (0< xs) of
  λ { 0ᵇ → 0ᵇ
    ; (0< ys) → 0< O∷ ys }
```

Without even thinking about dependent types, we can see that this function could
be improved.
In the last clause, we call `inc` recursively, and pattern match on its result.
However, as you can see from the other clauses in the function, this
pattern-match is redundant, because we *know* we'll never return `0ᵇ`.
A fix is simple:

```agda
inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0ᵇ = 1ᵇ
inc⁺ (0< 1ᵇ) = O∷ 1ᵇ
inc⁺ (0< O∷ xs) = I∷ xs
inc⁺ (0< I∷ xs) = O∷ inc⁺ (0< xs)

inc : 𝔹 → 𝔹
inc xs = 0< inc⁺ xs
```

This optimisation will also make it easier to prove things about `inc`: we don't
have to pattern match on the input now to find out that the output will be `0<`
something.
But we can go further: let's avoid re-wrapping the `xs` in the last clause of
`inc⁺`.

```agda
inc⁺⁺ : 𝔹⁺ → 𝔹⁺
inc⁺⁺ 1ᵇ = O∷ 1ᵇ
inc⁺⁺ (O∷ xs) = I∷ xs
inc⁺⁺ (I∷ xs) = O∷ inc⁺⁺ xs

inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0ᵇ = 1ᵇ
inc⁺ (0< xs) = inc⁺⁺ xs

inc : 𝔹 → 𝔹
inc xs = 0< inc⁺ xs
```

What we're effectively doing here is writing one function per piece of
information gained by pattern-matching.
We do it in Haskell as well.
Consider the following implementation of `last`:

```haskell
last :: [a] -> a
last [] = error "last: empty list"
last (x:[]) = x
last (x:xs) = last xs
```

The first clause checks if the outer list is empty, raising an error if so.
The second clause "knows" that the list isn't empty (if it was we wouldn't have
reached this point), and then checks if the tail is empty.
If it's not, we go to the third clause, and call `last` recursively with the
tail.
There's the issue: in the recursive call we'll (unnecessarily) check if the tail
is empty a second time, when we already *know* that it can't be empty.
We can remove the unnecessary check like so:

```haskell
last :: [a] -> a
last [] = error "last: empty list"
last (x:xs) = go x xs
  where
    go x [] = x
    go _ (x:xs) = go x xs
```

This optimisation is known as *call-pattern specialisation*, and GHC performs it
automatically these days [@jones_call-pattern_2007].
I find myself using it constantly in Agda: not only does it make things easier
to prove, it helps the termination checker, makes it easier to find bugs, allows
for more precise specification of functions, etc.

Unfortunately, it doesn't seem to speed things up in Agda. I'm not sure why, but
my hunch (at the moment) is that function calls are quite expensive for Agda,
whereas pattern-matches are cheap.

Finally, we can go one step further, by decomposing the datatypes themselves.

```agda
data Bit : Set where
  O I : Bit

infixr 5 _∷_ 0<_
data 𝔹⁺ : Set where
  1ᵇ : 𝔹⁺
  _∷_ : Bit → 𝔹⁺ → 𝔹⁺

data 𝔹 : Set where
  0ᵇ : 𝔹
  0<_ : 𝔹⁺ → 𝔹
```

Again, this unfortunately will cause a slowdown. For me, though, it was worth it
in terms of the cleaner proofs.

# Ordering on Binary Numbers

The next trick is for "irrelevant" proofs.
I've talked about Agda's notion of
["irrelevance"
](https://agda.readthedocs.io/en/v2.5.4.2/language/irrelevance.html) before
(mainly about how I misunderstood it). 
In short, this is *not* the same thing as
irrelevance in Haskell or Idris: in Haskell, all types are irrelevant, as you
cannot pattern match on them, or use them for computation.
Idris behaves similarly for a subset of types [@brady_inductive_2004].

For Agda, irrelevance means that a value is completely determined by its type.
It's handy for proofs in this way: you can rely on their existence or
non-existence, while knowing that they won't be around to slow you down at
runtime.

There are two ways to do irrelevance in Agda these days:
[`Prop`](https://agda.readthedocs.io/en/latest/language/prop.html) is a new sort
which is definitionally irrelevant, but the old way (by preceding definitions
with a `.`) still available.
