---
title: Type-Level Maps in Haskell
tags: Haskell
bibliography: Type-Level Maps.bib
---

Often, when describing the benefits of dependent types[^ml], people will focus on
proving things about programs, and how dependent types can provide guarantees
about correctness which are stronger than tests alone. In practice, though,
proving properties about your programs can be a pain: the proofs are long and
tedious, they are tightly coupled to implementations, and they often require
duplication of common structures with verified and unverified versions. A lot of
this is changing, but in Agda, Idris, and (to some extent) Haskell today,
quickcheck-style property testing (and Liquid Haskell) seem (to me) to be much
better options for verification.

[^ml]: I'm talking specifically about Martin-Löf types here, as that's the only
    system I have real experience with.

Proving things is only a small part of what dependent types can do, though. In
modern Haskell, dependent types allow us to say what we *mean*, often in a
simpler and more elegant way. Today, I'm going to go through one of those
applications today.

# State and Zooms

In Haskell, the way you're often told we do state is with the "state monad". So
where in python, you may have some function like this:

```python
def pop_3(xs):
  # Pops the last three elements from a list and returns their
  # sum.
  
  x = xs.pop()
  y = xs.pop()
  z = xs.pop()
  return x + y + z
```

The equivalent in Haskell might look something like this:

```haskell
pop :: State [a] a
pop = state (\(x:xs) -> (x, xs))

pop3 :: State [Integer] Integer 
pop3 = do
  x <- pop
  y <- pop
  z <- pop
  return (x + y + z)
```

But this has one massive limitation: *we only get one variable*. If we want more
than one, we could use a record, or tuples, but we quickly lose readability. So,
while the state monad kind of gives us an emulation of one of the features of
imperative programming, it's not entirely as powerful.

Here's another example: the reader monad provides *configuration*. Global,
immutable variables, in other words. However, if we have more than one
configuration variable, we've got the same problem as above: we can make a giant
record, and access each field for each "configuration variable", but again,
readability goes down. Also, *purity* is reduced. Not really, of course: the
reader and state monads are pure in reality, but in terms of style. If you have
a single record containing all of you configuration variables you lose some of
the information in the types that certain functions only rely on certain
configuration variables.

For both of these things, what we really want is a type-level mapping of field
names to types, and a value-level representation which goes with this. In other
words, a *type-level-map*.

# Type-Level Maps

The first question to ask ourselves is what kind of "map" are we going to use. A
red-black tree? AVL? If this were Idris or Agda, we could simply use Data.Map in
all of its optimized and tested glory: unfortunately, since Haskell doesn't yet
have fully dependent types, we're going to have to duplicate a *lot* of code
first.

So we'll build our own mapping structure. Here's the problem with using a tree
like a red-black tree, or AVL, or the tree of bounded balance that Data.Map
uses: the internal structure isn't order-independent. In other words:

```haskell
xs = fromList [("a",1),("b",2),("c",3)]
ys = fromList [("c",3),("b",2),("a",1)]
```

While `xs == ys` will return true, their internal representations are not
necessarily the same. This isn't a problem for Data.Map usually, since we can't
usually look a its internal representation, but it is a problem for our
type-level maps. If a function expects something with the type `fromList
[("a",1),("b",2),("c",3)]`, then it will only accept things with types that are
*propositionally equal* to that type. There are ways to get around this, with
quotient types and so on, but it's cumbersome even in languages like Agda.

So we need a data structure that has the property of *unique representation*. In
other words, it has to have the same internal structure for the same elements,
no matter how they're inserted.

One such data structure is described in @tarjan_unique_1989. Luckily, the
structure is purely functional, also. Unfortunately, it's quite complex, so
we're going to instead use lists. All the operations will be linear, but since
we're dealing with relatively small maps it should be fine.

Let's get started then. First, we're going to make our own pair type:

```haskell
infixr 6 :&
data a & b = a :& b
```

We're using this over standard tuples because the `(,)` syntax is duplicated at
the type level and value level, so you have to differentiate by writing `'(x,y)`
when you want to refer to a value. This is a little ugly.

Next, we want some standard map-like operations:

```haskell
type family Insert (x :: Symbol & Type) (xs :: [Symbol & Type]) :: [Symbol & Type] where
    Insert x '[] = x : '[]
    Insert (x :& xt) (y :& yt : ys) = Insert' (x :& xt) (y :& yt) (CmpSymbol x y) ys

type family Insert' (x :: Symbol & Type)
                    (y :: Symbol & Type)
                    (cmp :: Ordering)
                    (ys :: [Symbol & Type]) :: [Symbol & Type] where
    Insert' x y LT ys = x : y : ys
    Insert' x y EQ ys = x : ys
    Insert' x y GT ys = y : Insert x ys

type family FromList (xs :: [Symbol & Type]) :: [Symbol & Type] where
    FromList '[] = '[]
    FromList (x : xs) = Insert x (FromList xs)
```
