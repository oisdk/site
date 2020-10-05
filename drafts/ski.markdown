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

