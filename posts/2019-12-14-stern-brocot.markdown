---
title: Lazy Constructive Numbers and the Stern-Brocot Tree
tags: Haskell, Agda
bibliography: Rationals.bib
---

In dependently typed languages, it's often important to figure out a good
"low-level" representation for some concept.
The natural numbers, for instance:

```haskell
data Nat = Z | S Nat
```

For "real" applications, of course, these numbers are offensively inefficient,
in terms of both space and time.
But that's not what I'm after here: I'm looking for a type which best describes
the essence of the natural numbers, and that can be used to prove and think
about them.
In that sense, this representation is second to none: it's basically the
simplest possible type which *can* represent the naturals.

Let's nail down that idea a little better.
What do we mean when a type is a "good" representation for some concept.

-  There should be no redundancy.
   The type for the natural numbers above has this property: every natural
   number as one (and only one) canonical representative in `Nat`.
   Compare that to the following possible representation for the integers:
   ```haskell
   data Int = Neg Nat | Pos Nat
   ```
   There are two ways to represent `0` here: as `Pos Z` or `Neg Z`.
   
   Of course, you can quotient out the redundancy in Cubical Agda, or normalise
   on construction every time, but either of these workarounds gets your
   representation a demerit.

-  Operations should be definable simply and directly on the representation.
   Points docked for converting to and from some non-normalised form.
   
-  That conversion, however, can exist, and ideally should exist, in some
   fundamental way.
   You should be able to establish an efficient isomorphism with other
   representations of the same concept.

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

If you're going to deal with redundant elements, there are two broad ways to
deal with it.
Data.Ratio's approach is to normalise on construction, and only export a
constructor which does this.
This gives you a pretty good guarantee that there won't be any unreduced
fractions lying around in you program.
Agda's standard library also uses an approach like this, although the fact that
the numerator and denominator are coprime is statically verified by way of a
proof carried in the type.

The other way to deal with redundancy is by quotient.
In Haskell, that kind of means doing the following:

```haskell
instance Eq Frac where
  (x :/ xd) == (y :/ yd) = (x * yd) == (y * xd)
  
instance Ord Frac where
  compare (x :/ xd) (y :/ yd) = compare (x * yd) (y * xd)
```

We don't have real quotient types in Haskell, but this gets the idea across: we
haven't normalised our representation internally, but as far as anyone *using*
the type is concerned, they shouldn't be able to tell the difference between
$\frac{1}{2}$ and $\frac{2}{4}$.

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

Cubical Agda, of course, *does* have real quotient types.
There, the `Eq` instance becomes a path constructor.

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
Commons.](https://upload.wikimedia.org/wikipedia/commons/3/37/SternBrocotTree.svg)

This tree, pictured above, has some incredible properties:

* It contains every rational number (in reduced form) exactly once.
* It is a binary search tree.

Both of these properties make it an excellent candidate for basing a
representation on.
As it turns out, that's what we already did!
Our list of bits above is precisely a path into the Stern-Brocot tree, where
every `O` is a left turn and every `I` right.

# Incrementalising

The most important fact we've gleaned so far from the Stern-Brocot tree is that
our representation is lexicographically ordered.
While that may not seem like much, it turns our list of bits into a
progressively-narrowing interval, which generates more and more accurate
estimates of the true value.
When we see a `O` at the head of the list, we know that the result must be
smaller than `1`; what follows will tell us on what side of $\frac{1}{2}$ the
answer lies, and so on.

This turns out to be quite a useful property: we often don't need *exact*
precision for some calculation, but rather some approximate answer.
It's even rarer still that we know exactly how much precision we need for a
given expression (which is what floating point demands).
Usually, the precision we need changes quite dynamically.
If a particular number plays a more influential role in some expression, for
instance, its precision is more important than the others!

By producing a lazy list of bits, however, we can allow the *consumer* to
specify the precision they need, by demanding those bits as they go along.
(In the literature, this kind of thing is referred to as "lazy exact
arithmetic", and it's quite fascinating. 
The representation presented here, however, is not very suitable for any real
computation: it's incredibly slow.
There is a paper on the topic: @niquiExactArithmeticStern2007, which examines
the Stern-Brocot numbers in Coq).

In proofs, the benefit is even more pronounced: finding out that a number is in
a given range by just inspecting the first element of the list gives an
excellent recursion strategy.
We can do case analysis on: "what if it's 1", "what if it's less than 1", and
"what if it's greater than 1", which is quite intuitive.

There's one problem: our evaluation function is defined as a `foldr`, and forces
the accumulator at every step.
We will need to figure out another evaluator which folds from the left.

# Intervals

So let's look more at the "interval" interpretation of the Stern-Brocot tree.
The first interval is $\left(\frac{0}{1},\frac{1}{0}\right)$: neither of these
values are actually members of the type, which is why we're not breaking any
major rules with the $\frac{1}{0}$.
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

From this, we get a straightforward left fold which can compute our fraction.

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
\right) \;
R = 
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

# Incrementalising!

We now have all the parts we need.
First, we will write an evaluator that returns increasingly precise intervals.
Our friend `scanl` fits the requirement precisely.

```haskell
approximate :: [Bit] -> [Interval]
approximate = scanl f mempty
  where
    f i I = right i
    f i O = left  i
```

Next, we will need to combine two of these lists with some operation on
fractions.

```haskell
interleave :: (Frac -> Frac -> Frac)
           -> [Interval]
           -> [Interval]
           -> [Interval]
interleave (*) [xi] ys = map (\y -> x * lb y :-: x * ub y) ys
  where x = mediant xi
interleave (*) (x:xs) ys@(y:_) =
  (((*) `on` lb) x y :-: ((*) `on` ub) x y) : interleave (*) ys xs
```

The operation must respect orders in the proper way for this to be valid.

This pops one bit from each list in turn: one of the many possible optimisations
would be to pull more information from the more informative value, in some
clever way.

Finally, we have a function which incrementally runs some binary operator
lazily on a list of bits.

```haskell
quad :: (Frac -> Frac -> Frac)
     -> [Bit]
     -> [Bit]
     -> [Bit]
quad (*) xs ys = foldr f (unfoldr p) zs mempty
  where
    zs = (interleave (*) `on` approximate) xs ys
    
    f x xs c
      | mediant c < lb x = I : f x xs (right c)
      | mediant c > ub x = O : f x xs (left  c)
      | otherwise = xs c
        
    t = mediant (last zs)
    
    p c = case compare (mediant c) t of
      LT -> Just (I, right c)
      GT -> Just (O, left  c)
      EQ -> Nothing
```

The function only ever inspects the next bit when it absolutely needs to.

The helper function `f` here is the "incremental" version.
`p` takes over when the precision of the input is exhausted.

We can use this to write an addition function (with some added special cases to
speed things up).

```haskell
add :: [Bit] -> [Bit] -> [Bit]
add [] ys = I : ys
add xs [] = I : xs
add (I:xs) ys = I : add xs ys
add xs (I:ys) = I : add xs ys
add xs ys = quad (+) xs ys
```

We (could) also try and optimise the times we look for a new bit.
For addition, if two strings are inverses of each other, the result will be
precisely in the middle.
i.e. `OIOOI` + `IOIIO` = $\frac{1}{1}$.
We could try and spot this, only testing with comparison of the mediant when the
bits are the same.
You've doubtless spotted some other possible optimisations: I have yet to look
into them!

# Inverting Functions

One of the other applications of lazy rationals is that they can begin to *look*
like the real numbers.
For instance, the `p` helper function above is basically defined extensionally.
Instead of stating the value of the number, we give a function which tells us
when we've made something too big or too small (which sounds an awful lot like a
Dedekind cut to my ears).
Here's a function which *inverts* a given function on fractions, for instance.

```haskell
inv :: (Frac -> Frac) -> [Bit] -> [Bit]
inv o n = unfoldr f mempty
  where
    t = fromQ n
    
    f c = case compare (o (mediant c)) t of
      LT -> Just (I, right c)
      GT -> Just (O, left  c)
      EQ -> Nothing
```

Of course, the function has to satisfy all kinds of extra properties that I
haven't really thought a lot about yet, but no matter.
We can use it to invert a squaring function:

```haskell
sqrt :: [Bit] -> [Bit]
sqrt = inv (\x -> x * x)
```

And we can use *this* to get successive approximations to $\sqrt{2}$!

```haskell
root2Approx
  = map (toDouble . mediant) (approximate (sqrt (abs (2 :/ 1))))
  
>>> mapM_ print root2Approx
1.0
2.0
1.5
1.3333333333333333
1.4
1.4285714285714286
1.4166666666666667
1.411764705882353
1.4137931034482758
1.4146341463414633
...
```

# Conclusions and Related Work

Using the Stern-Brocot tree to represent the rationals was formalised in Coq in
@bertotSimpleCanonicalRepresentation2003.
The corresponding lazy operations are formalised in
[QArith](https://github.com/coq-community/qarith-stern-brocot).
Its theory and implementation is described in @niquiExactArithmeticStern2007.
Unfortunately, I found most of the algorithms impenetrably complex, so I can't
really judge how they compare to the ones I have here.

I mentioned that one of the reasons you might want lazy rational arithmetic is
that it can help with certain proofs.
While this is true, in general the two main reasons people reach for lazy
arithmetic is efficiency and as a way to get to the real numbers.

From the perspective of efficiency, the Stern-Brocot tree is probably a bad
idea.
You may have noticed that the right branch of the tree contains all the whole
numbers: this means that the whole part is encoded in unary.
Beyond that, we generally have to convert to some fraction in order to do any
calculation, which is massively expensive.

The problem is that bits in the same position in different numbers don't
necessarily correspond to the same quantities.
In base 10, for instance, the numbers 561 and 1024 have values in the "ones"
position of 1 and 4, respectively.
We can work with those two values independent of the rest of the number, which
can lead to quicker algorithms.

Looking at the Stern-Brocot encoding, the numbers $\frac{2}{3}$ and 3 are
represented by `OI` and `II`, respectively.
That second `I` in each, despite being in the same position, corresponds to
*different values*: $\frac{2}{3}$ in the first, and $\frac{1}{2}$ in the second.

Solutions to both of these problems necessitate losing the one-to-one property
of the representation.
We could improve the size of the representation of terms by having our $L$ and
$R$ matrices be the following [@kurkaExactRealArithmetic2014]:

$$ L = \left( 
\begin{matrix}
  1 & 0 \\
  1 & 2
\end{matrix}
\right) \;
 R = \left( 
\begin{matrix}
  2 & 1 \\
  0 & 1
\end{matrix}
\right) $$

But now there will be gaps in the tree.
This basically means we'll have to use infinite repeating bits to represent
terms like $\frac{1}{2}$.

We could solve the other problem by throwing out the Stern-Brocot tree entirely
and using a more traditional positional number system.
Again, this introduces redundancy: in order to represent some fraction which
doesn't divide properly into the base of the number system you have to use
repeating decimals.

The second reason for lazy rational arithmetic is that it can be a crucial
component in building a constructive interpretation of the real numbers.
This in particular is an area of real excitement at the moment: HoTT has opened
up some interesting avenues that weren't possible before for constructing the
reals [@bauerRealNumbersHomotopy2016].

In a future post, I might present a formalisation of these numbers in Agda.
I also intend to look at the dyadic numbers.

# References
