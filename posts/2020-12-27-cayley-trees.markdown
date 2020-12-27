---
title: Trees indexed by a Cayley Monoid
tags: Haskell
---

The Cayley monoid is well-known in Haskell (difference lists, for instance, are
a specific instance of the Cayley monoid), because it gives us $O(1)$ `<>`.
What's less well known is that it's also important in dependently typed
programming, because it gives us definitional associativity.
In other words, the type `x . (y . z)` is definitionally equal to `(x . y) . z`
in the Cayley monoid.

<details>
<summary>Some helpers and extra code</summary>

```haskell
data Nat = Z | S Nat

type family (+) (n :: Nat) (m :: Nat) :: Nat where
  Z   + m = m
  S n + m = S (n + m)
```
</details>

I used a form of the type-level Cayley monoid in a [previous
post](2020-02-15-taba.html) to type vector reverse without proofs.
I figured out the other day another way to use it to type tree flattening.

Say we have a size-indexed tree and vector:

```haskell
data Tree (a :: Type) (n :: Nat) :: Type where
  Leaf  :: a -> Tree a (S Z)
  (:*:) :: Tree a n -> Tree a m -> Tree a (n + m)

data Vec (a :: Type) (n :: Nat) :: Type where
  Nil  :: Vec a Z
  (:-) :: a -> Vec a n -> Vec a (S n)
```

And we want to flatten it to a list in $O(n)$ time:

```haskell
treeToList :: Tree a n -> Vec a n
treeToList xs = go xs Nil
  where
    go :: Tree a n -> Vec a m -> Vec a (n + m)
    go (Leaf    x) ks = x :- ks
    go (xs :*: ys) ks = go xs (go ys ks)
```

Haskell would complain specifically that you hadn't proven the monoid laws:

    • Couldn't match type ‘n’ with ‘n + 'Z’
    • Could not deduce: (n2 + (m1 + m)) ~ ((n2 + m1) + m)
    
But it seems difficult at first to figure out how we can apply the same trick as
we used for vector reverse: there's no real way for the `Tree` type to hold a
function from `Nat` to `Nat`.

To solve this problem we can borrow a trick that Haskellers had to use in the
good old days before type families to represent type-level functions: types (or
more usually classes) with multiple parameters.

```haskell
data Tree' (a :: Type) (n :: Nat) (m :: Nat) :: Type where
  Leaf  :: a -> Tree' a n (S n)
  (:*:) :: Tree' a n2 n3
        -> Tree' a n1 n2
        -> Tree' a n1 n3
```

The `Tree'` type here has three parameters: we're interested in the last two.
The first of these is actually an argument to a function in disguise; the second
is its result.
To make it back into a normal size-indexed tree, we apply that function to zero:

```haskell
type Tree a = Tree' a Z

three :: Tree Int (S (S (S Z)))
three = (Leaf 1 :*: Leaf 2) :*: Leaf 3
```

This makes the `treeToList` function typecheck without complaint:

```haskell
treeToList :: Tree a n -> Vec a n
treeToList xs = go xs Nil
  where
    go :: Tree' a x y -> Vec a x -> Vec a y
    go (Leaf    x) ks = x :- ks
    go (xs :*: ys) ks = go xs (go ys ks)
```
