---
title: Fun with SKI
tags: Haskell
---

<script src="../code/ski/script.js"></script>

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

There are only three combinators in SKI: S, K, and I (shocking, I know).
These operate on strings and each of them do different things:

```
Sxyz ~> xz(yz)
Kxy  ~> x
Ix   ~> x
```

I'll explain the actual form rules in a second, but first let's work with some
examples to get a sense for how these combinators work.

Upper case letters are combinators, lower-case are variables.
Yes, yes, I know I said that SKI didn't need variables, and it doesn't!
I'm just using them here to explain how each of the combinators work.
If you really want to be pedantic you can think of the lower case letters as
notational placeholders meaning "any given combinator".
They won't exist in any actual programs we write with SKI.

Right, so the simplest combinator is `I`.
`I` is like the identity combinator: it just returns its first argument.
If you give a combinator more arguments than it usually accepts, you just keep
the extra arguments in the output:

```
Ixyz ~> xyz
Iyx  ~> yx
```

`K` is the next combinator: it is the "const" one.
It discards its second argument:

```
Kxyz ~> xz
```

We always start from the *left*, applying the rule for the left-most combinator
first.

```
KIxyz ~> Iyz  ~> yz
IKxyz ~> Kxyz ~> xz
```

If you don't give the leftmost combinator enough arguments, evaluation gets
stuck:

```
Kx ~> Kx
```

Here's a small little evaluator for expressions which use `I` and `K`.
You can edit the expression, and click "step" to step through it.

<p id="KI"></p><script>small_repl("KI", 2, "IKxyz", Comb.K,
Comb.I);</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

The last combinator introduces parentheses: it doesn't really have an intuitive
analogue in functions (technically it's `<*>` for the reader monad, which is
entirely unhelpful), but it works like this:

```
Sxyz ~> xz(yz)
```

Implicitly, all expressions are left-associative.
That means that the following are all equal:

```
xyz = (xy)z = (x)yz = ((x)y)z
```

But `xyz` is *not* equal to, say, `x(yz)`.

Here's another simple evaluator for SKI expressions which includes `S`:

<p id="SKI"></p><script>small_repl("SKI", 5, "SKIxyz", Comb.S, Comb.K,
Comb.I);</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

And here's a puzzle to start flexing your SKI skills: it turns out that SKI
isn't actually as simple as it could be!
One of the combinators can be defined in terms of the other two.
Use the evaluator above to try and figure out which it is, and its definition.

<details>
<summary>The Redundant Combinator</summary>
`I`
</details>

<details>
<summary>Its Definition</summary>
`I = SKK = SKS`
</details>
