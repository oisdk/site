---
title: Fun with SKI
tags: Haskell
---

There are a bunch of "minimal" computational models out there: Turing machines,
lambda calculus,
[powerpoint](https://www.andrew.cmu.edu/user/twildenh/PowerPointTM/Paper.pdf), etc.
Of those, lambda calculus is without question my favourite to actually write
programs in: despite being simple and minimal, it's actually not too far from a
workable language.

In terms of implementation, though, it is *far* from simple.
Lambda calculus has *variables*, which introduce huge complexity into the
interpreter: especially if you want to do any kind of formal reasoning about
programs, this complexity is a problem.
We might want to reach for something even lower-level than lambda calculus: this
is where SKI calculus comes in.

We can actually encode SKI in lambda calculus.
We start with the following definitions:

```
S = \x y z -> (x z) (y z)
K = \x y -> x
I = \x -> x
```

These three combinators actually correspond to the Applicative operations on the
Reader monad (`S = <*>`, `K = pure`, `I = ask`).
(don't worry if you don't understand this, it's not very important! Just an
interesting observation).

So, it turns out that from these three combinators we can actually construct
*any* lambda expression.
As an example, we actually don't even need `I`!
We can construct it from `S` and `K`:

```
I = S K K
  = \x -> S K K x
  = \x -> (K x) (K x)
  = \x -> x
```

# Interpreting SKI Expressions

# Parsing
