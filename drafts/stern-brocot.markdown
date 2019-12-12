---
title: Constructive Numbers and the Stern-Brocot Tree
tags: Haskell, Agda
bibliography: Rationals.bib
---

In dependently typed languages, it's often important to figure out a good
"low-level" representation for some concept.
The natural numbers, for instance:

```haskell
data Nat = Z | S Nat
```

Though it's easy in this case, figuring out a representation is often
nontrivial.
As well as having the type be interpretable as the thing it's meant to
represent, we also want it to have the following properties:

-  It should not have any redundancy.
   The type for the natural numbers above has this property: every natural
   number as one (and only one) canonical representative in `Nat`.
   Compare that to the following possible representation for the integers:
   ```haskell
   data Int = Neg Nat | Pos Nat
   ```
   There are two ways to represent `0` here: as `Pos Z` or `Neg Z`.
   There are obvious reasons this causes trouble (it tends to be bug-prone, as
   you tend to forget about the "other" case, and equality becomes a much weaker
   property), but my main concern is how it mucks up proofs.
   Also, we have failed at finding the "theoretically true" representative of
   the type.

-  Operations on the type should be easily expressible on its representation.
   Take addition on `Nat` above: it is straightforward and natural to define.

-  Properties about the type should correspond to intuitive properties about the
   representation.
   For `Nat` above, this means things like order: the usual order on the natural
   numbers again has a straightforward analogue on `Nat`.

With that laundry list of requirements, it's no wonder that it's often tricky to
figure out the "right" type for a concept.

In this post, I'm going to talk about a type for the rational numbers, and I'm
going to try satisfy those requirements as best I can.

# The Rationals as a Pair of Numbers

Our first attempt at representing the rationals might use a fraction:

```haskell
data Frac = Integer :/ Natural
```

This obviously fails the redundancy property.
The fractions $\frac{1}{2}$ and $\frac{2}{4}$ represent the same number, but
have different underlying values.

So the type isn't suitable as a potential representation for the rationals.
That's not to say that this type is useless: far from it!
Indeed, Haskell's
[Data.Ratio](https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Ratio.html)
uses something quite like this to implement rationals.

Here, we'll use it as a kind of intermediate representation.
To keep us (semantically) honest, though, we'll give it the proper `Eq` and
`Ord` instances.

```haskell
instance Eq Frac where
  (x :/ xd) == (y :/ yd) = (x * yd) == (y * xd)
  
instance Ord Frac where
  compare (x :/ xd) (y :/ yd) = compare (x * yd) (y * xd)
```

Th `Num` instance is pretty much just a restating of the axioms for fractions.

<details>
<summary>
`Num` instance for `Frac`.
</summary>

```haskell
instance Num Frac where
  fromInteger n = fromInteger n :/ 1
  (x :/ xd) * (y :/ yd) = (x * y) :/ (xd * yd)
  (x :/ xd) + (y :/ yd) = (x * yd + y * xd) :/ (xd * yd)
  signum = (:/ 1) . signum . numerator
  abs = id
  (x :/ xd) - (y :/ yd) = (x * yd - y * xd) :/ (xd * yd)
```
</details>

# The Rationals as a Pair of Coprime Numbers

Let's look a little more at Data.Ratio's approach.
What we did above was postpone the normalisation until we do operations on the
fraction.
Data.Ratio, on the other hand, does normalisation on construction, ensuring that
the fraction is only ever stored in its lowest form.
This is actually what Agda does in the standard library: each rational also
comes equipped with a proof that the two numbers are coprime, making it a "true"
type for the rationals.

Interestingly, the normalisation on testing approach is basically what we'd do
in Cubical Agda: our type might look something like this.

```agda
data ℚ : Type₀ where
  _÷_ : (n d : ℕ) → ℚ
  reduce : ∀ xⁿ xᵈ yⁿ yᵈ →
           xⁿ ℕ* yᵈ ≡ yⁿ ℕ* xᵈ →
           xⁿ ÷ xᵈ ≡ yⁿ ÷ yᵈ
```

But we'll leave the Agda stuff for another post.

# The Rationals as a Trace of Euclid's Algorithm

Now we get to the cool stuff.
To reduce a fraction, we usually do something like getting the greatest common
divisor of each operand.
One nice way to do that is to use Euclid's algorithm:

```haskell
gcd :: Natural -> Natural -> Natural
gcd n m = case compare n m of
  EQ -> n
  LT -> gcd n (m - n)
  GT -> gcd (n - m) m
```

Let's run that function on three different inputs: $\frac{2}{3}$, $\frac{4}{6}$,
and $\frac{5}{6}$.

```haskell
gcd 2 3 => case compare 2 3 of
  LT -> gcd 2 (3 - 2) => case compare 2 1 of
    GT -> gcd (2 - 1) 1 => case compare 1 1 of
      EQ -> 1

gcd 4 6 => case compare 4 6 of
  LT -> gcd 4 (6 - 4) => case compare 4 2 of
    GT -> gcd (4 - 2) 2 => case compare 2 2 of
      EQ -> 2

gcd 5 6 => case compare 5 6 of
  LT -> gcd 5 (6 - 5) => case compare 5 1 of
    GT -> gcd (5 - 1) 1 => case compare 4 1 of
      GT -> gcd (4 - 1) 1 => case compare 3 1 of
        GT -> gcd (3 - 1) 1 => case compare 2 1 of
          GT -> gcd (2 - 1) 1 => case compare 1 1 of
            EQ -> 1
```

Those all return the right things, but that's not what's interesting here: look
at the chain of comparison results.
For the two fractions which are equivalent, their *chains* are equal.

This turns out to hold in general. 
Every rational number can be (uniquely!) represented as a list of bits, where
each bit is a comparison result from Euclid's algorithm.

```haskell
data Bit = O | I

type Rational = [Bit]

abs :: Frac -> Rational
abs = unfoldr f
  where
    f (n :/ d) = case compare n d of
      EQ -> Nothing
      LT -> Just (O, n :/ (d - n))
      GT -> Just (I, (n - d) :/ d)
```

And since we used `unfoldr`, it's easy to reverse the algorithm to convert from
the representation to a pair of numbers.

```haskell
rep :: Rational -> Frac
rep = foldr f (1 :/ 1)
  where
    f I (n :/ d) = (n + d) :/ d
    f O (n :/ d) = n :/ (n + d)
```

Now `abs . rep` is the identity function, and `rep . abs` reduces a fraction!
We have identified an isomorphism between our type (a list of bits) and the
rational numbers!

Well, between the positive rational numbers. 
Not to worry: we can add a sign before it.
And, because our type doesn't actually include 0, we don't get the duplicate 0
problems we did with `Int`.

```haskell
data Q
  = Neg Rational
  | Zero
  | Pos Rational 


```

We can also define some operations on the type, by converting back and forth.

```haskell
instance Num Rational where
  fromInteger n = abs (fromInteger n :/ 1)
  
  xs + ys = abs (rep xs + rep ys)
  xs * ys = abs (rep xs * rep ys)
  xs - ys = abs (rep xs - rep ys)
```

# Rationals as a Path into The Stern-Brocot Tree

So we have a construction that has our desired property of canonicity.
Even better, there's a reasonably efficient algorithm to convert to and from it!
Our next task will be examining the representation itself, and seeing what
information we can get from it.

To do so we'll turn to the subject of the title of this post: the [Stern-Brocot
tree](https://en.wikipedia.org/wiki/Stern%E2%80%93Brocot_tree).

![The Stern-Brocot Tree. By Aaron Rotenberg, CC BY-SA 3.0, from Wikimedia
Commons.](/images/SternBrocotTree.svg)

This tree, pictured above, has some incredible properties:

* It contains every rational number (in reduced form) exactly once.
* It is a binary search tree.

Both of these properties make it an excellent candidate for basing a
representation on.
As it turns out, that's what we already did!
Our list of bits above is precisely a path into the Stern-Brocot tree, where
every `O` is a left turn and every `I` right.
This gives us a very useful piece of information: the list of bits we have above
is lexicographically ordered on the rationals.

# Incrementalising

Probably the most intriguing aspect of the Stern-Brocot tree (for our purposes)
is the fact that it is a binary search tree.
This gives us an easy way to express an order on the binary representation, but
more interestingly it can allow us to *incrementalise* computation somewhat.
Consider adding $\frac{1}{3}$ and $\frac{4}{3}$.
They are represented by the binary sequences `00` and `100`, respectively.
When looking out what to output, we don't need to inspect the entire inputs:
once we see the `1` from $\frac{4}{3}$ we know that we're going to be outputting
a number above 1, so we'll output a `1` at that point.

We're going to have some difficulty in trying to generalise this, though.
Our main problem comes from the way we convert a bit sequence to a fraction: we
`foldr` over it, and we inspect the accumulator at every step.
That means the function isn't nearly lazy enough to give us proper incremental
computation.
We need a way to computer the fraction that uses a *left* fold.

# Intervals

So we need another way to convert our list of bits to a fraction.
The tree above will help us here: every step down can be thought of as a
narrowing function, reducing the size of some interval as you go.
The first interval is $\left(\frac{0}{1},\frac{1}{0}\right)$.
To move left (to $\frac{1}{2}$ in the diagram), we need to use a peculiar
operation called "child's addition", often denoted with a $\oplus$.

$$ \frac{a}{b} \oplus \frac{c}{d} = \frac{a+c}{b+d} $$

The name comes from the fact that it's a very common mistaken definition of
addition on fractions.

Right, next steps: to move *left* in an interval, we do the following:

$$ \text{left} \left(\mathit{lb},\mathit{ub} \right) = \left( \mathit{lb}, \mathit{lb} \oplus \mathit{ub} \right) $$

In other words, we narrow the right-hand-side of the interval.
To move right is the opposite:

$$ \text{right} \left(\mathit{lb},\mathit{ub} \right) = \left( \mathit{lb}
\oplus \mathit{ub} , \mathit{ub} \right) $$

And finally, when we hit the end of the sequence, we take the *mediant* value.

$$ \text{mediant}\left(\mathit{lb} , \mathit{ub}\right) = \mathit{lb} \oplus
\mathit{rb} $$

From this, we get a straightforward left fold which can computer our fraction!

```haskell
infix 6 :-:
data Interval
  = (:-:)
  { lb :: Frac
  , ub :: Frac
  }

mediant :: Interval -> Frac
mediant (b :/ d :-: a :/ c) = (a+b) :/ (c+d)

left, right :: Interval -> Interval
left  x = lb x :-: mediant x
right x = mediant x :-: ub x

rep' :: [Bit] -> Frac
rep' = mediant . foldl f ((0 :/ 1) :-: (1 :/ 0))
  where
    f a I = right a
    f a O = left a
```

# Monoids and Matrices

Before diving in and using this new evaluator to incrementalise our functions,
let's take a look at what's going on behind the scenes of the "interval
narrowing" idea.

It turns out that the "interval" is really a $2\times2$ square matrix in
disguise (albeit a little reordered).

$$ \left( \frac{a}{b} , \frac{c}{d} \right) =
\left(
\begin{matrix} 
  c & a \\ 
  d & b
\end{matrix} 
\right)
$$

Seen in this way, the beginning interval---$\left(\frac{0}{1} ,
\frac{1}{0}\right)$---is actually the identity matrix.
Also, the two values in the second row of the tree correspond to special
matrices which we will refer to as $L$ and $R$.

$$ L = 
\left(
\begin{matrix} 
  1 & 0 \\ 
  1 & 1
\end{matrix} 
\right)
$$
$$ R = 
\left(
\begin{matrix} 
  1 & 1 \\ 
  0 & 1
\end{matrix} 
\right)
$$

It turns out that the left and right functions we defined earlier correspond to
multiplication by these matrices.

$$ \text{left}(x) = Lx $$
$$ \text{right}(x) = Rx $$

Since matrix multiplication is associative, what we have here is a monoid.
`mempty` is the open interval at the beginning, and `mappend` is matrix
multiplication.
This is the property that lets us incrementalise the whole thing, by the way:
associativity allows us to decide when to start and stop the calculation.
