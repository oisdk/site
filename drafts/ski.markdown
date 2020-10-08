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

<p id="KI"></p><script>
small_repl(
  { input_id: "KI"
  , output_lines: 2
  , initial_expr: "IKxyz"
  , allowed_combos: [Comb.K, Comb.I]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

The last combinator introduces parentheses: it doesn't really have an intuitive
analogue in functions (technically it's `<*>` for the reader monad, which is
entirely unhelpful), but it works like this:

```
Sxyz ~> xz(yz)
```

You can write parentheses yourself: implicitly, all expressions are left-associative.
That means that the following are all equal:

```
xyz = (xy)z = (x)yz = ((x)y)z
```

But `xyz` is *not* equal to, say, `x(yz)`.

And here's a puzzle to start flexing your SKI skills: it turns out that SKI
isn't actually as simple as it could be!
Technically speaking, we don't need `I`, as it can be defined in terms of `S`
and `K`.
Use the following evaluator to try and figure out how to do it: write an
expression into the box that, when applied to `x`, evaluates to `x`.
You're only allowed to use `S`, `K`, and parentheses for this.

<p id="SKI"></p><script>
small_tester(
  { input_id: "SKI"
  , output_lines: 5
  , initial_expr: ""
  , vars: "x"
  , expect: "x" 
  , allowed_combos: [Comb.S, Comb.K]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

<details><summary>The Answer</summary>
`I = SKK = SKS`
</details>

# Some Other Combinators

We have a good reason for focusing on the `S` and `K` combinators: together,
they're Turing complete, and they're the simplest two combinators which have
that property (I think).
Other combinators are either weirder, or require more than two to get Turing
completeness.

All the same, they are not very intuitive or usable.
We're going to look at two other combinator sets now which are equal in power to
the SK combinators: they have four combinators a piece, though, so they're not
as "simple".

First, we have the `BAMT` combinator set.
I'll give the definition of each first, and then we'll move on to exploring them
a little.

```
Bxyz ~> x(yz)
Axy  ~> y
Mx   ~> xx
Txy  ~> yx
```

`A` is quite similar to `K`, but it drops is first argument, keeping the
second^[If you want to look up these combinators elsewhere, this is the only one
you won't be able to find: it's much less common than `K`, and where I have
found it people just call it `K`, so I had to pick a different letter to
distinguish it].
`M` duplicates its argument, and `T` swaps them around.
`B`, like `S`, adds parentheses.

In terms of normal functional code, `B` is composition: it takes two functions
and an argument, and applied those two functions to the argument.

I quite like this combinator set because each combinator is extremely simple in
its function.
Also, each combinator gives a concrete capability to the combinators.
`M`, for instance, allows us to make copies.
If we worked with only the `BAT` combinators, we would know that our interpreter
would always produce an output no larger than its input.
Similarly, `A` allows us to discard information.

A combinator system that didn't include the `A` or `M` combinators would be
*linear*: in fact, some linear logic (and affine logic) systems are based on
this precise symmetry.

So now, let's try use some of them to replicate the `SKI` combinators.
First, `I` (you want to write an expression that, when applied to `x`, returns
`x`):

<p id="BAMTtoI"></p><script>
small_tester(
  { input_id: "BAMTtoI"
  , output_lines: 2
  , initial_expr: ""
  , vars: "x"
  , expect: "x" 
  , allowed_combos: [Comb.B, Comb.A, Comb.M, Comb.T]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

<details><summary>The Answer</summary>
`A` followed by anything (so `AB`, `AT`, `AM`, etc) will give you a combinator
equivalent to `I`.
</details>

That should have been pretty easy.
The next one is *not*: do not expect to be able to get it!
You need to replicate `K`.

<p id="BAMTtoK"></p><script>
small_tester(
  { input_id: "BAMTtoK"
  , output_lines: 5
  , initial_expr: ""
  , vars: "xy"
  , expect: "x" 
  , allowed_combos: [Comb.B, Comb.A, Comb.M, Comb.T]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

<details><summary>The Answer</summary>
Either of the following would work:

```
B(TA)(BBT)
B(B(TA)B)T
```
</details>

That last one was pretty ugly.
`S` is even more horrific still:

```
S = B(B(B(T(BM(BBT)))(BBT)))(BB(B(T(BBT))(BBT)))
```

You can try out the `BAMT` calculus in the following evaluator, it's loaded up
with the awful equivalence for `S`:

<p id="BAMTtoS"></p><script>
small_repl(
  { input_id: "BAMTtoS"
  , output_lines: 5
  , initial_expr: "B(B(B(T(BM(BBT)))(BBT)))(BB(B(T(BBT))(BBT)))xyz"
  , allowed_combos: [Comb.B, Comb.A, Comb.M, Comb.T]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

# A Usable Combinator Set

So we've seen the theoretically simple `SK` combinators, the simple to
understand (but a nightmare to use) `BAMT` combinators, now we'll introduce a
combinator set which is relatively simple to both understand *and* use: `BCKW`.

```
Bxyz ~> x(yz)
Cxyz ~> xzy
Kxy  ~> x
Wxy  ~> xyy
```

You can see that it's a little similar to `BAMT`, we have `B`, we have `K`
(which is quite similar to `A`), and the `C` and `W`.
These last two function analogously to `T` and `M`, except they take an extra
argument that they keep in front.
This makes them *far* easier to use.
Here's a repl to try them out.
See if you can figure out the other combinators we've seen so far.

<p id="BCKW"></p><script>
small_repl(
  { input_id: "BCKW"
  , output_lines: 5
  , initial_expr: ""
  , allowed_combos: [Comb.B, Comb.C, Comb.K, Comb.W]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>


And here's a puzzle: this is difficult, but doable.
See if you can express `S` using `BCKW` alone.

<p id="BCKWtoS"></p><script>
small_tester(
  { input_id: "BCKWtoS"
  , output_lines: 5
  , initial_expr: ""
  , vars: "xyz"
  , expect: "xz(yz)"
  , allowed_combos: [Comb.B, Comb.C, Comb.K, Comb.W]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

<details><summary>The Answer</summary>
```
S = B(BW)(BBC)
```
</details>
