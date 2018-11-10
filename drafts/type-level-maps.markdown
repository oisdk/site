---
title: Type-Level Maps in Haskell
tags: Haskell
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
than one, we could use a record, or tuples, but we quickly lose readability.

Here's another example: the reader monad provides *configuration*. Global,
immutable variables, in other words. However, if we have more than one
configuration variable, 
