---
title: Constructive Numbers and the Stern-Brocot Tree
tags: Haskell, Agda
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
data Frac = Natural :/ Natural
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
For the `Frac` type above, we overloaded the `==` function to do what we wanted.
Another approach would be to only permit users to construct a fraction in
reduced form.
In other words we wouldn't export the `:/` constructor, but rather a smart
constructor which would first reduce its two arguments.

This choice isn't perfect either: but it *is* what's used in Agda's standard
library (where the rationals carry a proof that the two numbers are coprime),
and it's relatively easy to understand.

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

# Rationals as a Path into The Stern-Brocot Tree

Let's now turn to the subject of the title of this post: the [Stern-Brocot
tree](https://en.wikipedia.org/wiki/Stern%E2%80%93Brocot_tree).

![The Stern-Brocot Tree. By Aaron Rotenberg, CC BY-SA 3.0, from Wikimedia
Commons.](https://upload.wikimedia.org/wikipedia/commons/3/37/SternBrocotTree.svg)

This tree, pictured above, has some incredible properties:

* It contains every rational number (in reduced form) exactly once.
* It is a binary search tree.

Both these
