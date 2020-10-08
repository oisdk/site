---
title: Fun with Combinator Calculi
tags: Haskell
---

<script src="../code/ski/script.js"></script>
<style>
input[type=text] {
    border:0;
    outline:0;
    font-size: 11px;
    font-family: menlo, monospace;
}
input[type=text]:focus {
    outline:none!important;
}
input[type=text]:invalid {
    color: red;
    box-shadow: none;
}
</style>

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
is where combinator calculi come in.

You may have heard of SKI combinator calculus: it's the "simplest" of the
calculi, but it's not actually very easy to understand, and it's absolute murder
to try use.
So we're going to start with BCKW, a more obscure calculus, actually invented by
Haskell Curry.

There are 4 combinators in BCKW: B, C, K, and W (shocking, I know).
You can think about these combinators as functions which manipulate the
beginning of strings:

```
Bxyz ~> x(yz)
Cxyz ~> xzy
Kxy  ~> x
Wxy  ~> xyy
```

I'll explain the actual formal rules in a second, but first let's work with some
examples to get a sense for how these combinators work.

Upper case letters are combinators, lower-case are variables.
Yes, yes, I know I said that combinator calculi didn't need variables, and it
doesn't!
I'm just using them here to explain how each of the combinators work.
If you really want to be pedantic you can think of the lower case letters as
notational placeholders meaning "any given combinator".
They won't exist in any actual programs we write.

The simplest combinator is `K`: it's actually equivalent to the  `const`
function from Haskell.
It discards its second argument, and returns the first.
If you give a combinator more arguments than it usually accepts, you just keep
the extra arguments in the output:

```
Kxyz ~> xz
```

`W` is the next combinator: it *duplicates* its second argument.

```
Wxy ~> xyy
```

We always start from the *left*, applying the rule for the left-most combinator
first.

```
WKxyz ~> Kxxyz ~> xyz
KWxyz ~> Wyz   ~> yzz
```

Next we have `C`: this is equivalent to the Haskell function `flip`.
It swaps the second and third arguments:

```
Cxyz ~> xzy
```

Here's a small little evaluator for expressions which use `C`, `K`, and `W`.
You can edit the expression, and press enter to step through it.

<p id="CKW"><script>
small_repl(
  { input_id: "CKW"
  , output_lines: 3
  , initial_expr: "WKCxyz"
  , allowed_combos: [Comb.C, Comb.K, Comb.W]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

The last combinator introduces parentheses, and it's equivalent to function
composition.

```
Bxyz ~> x(yz)
```

You can write parentheses yourself: implicitly, all expressions are left-associative.
That means that the following are all equal:

```
xyz = (xy)z = (x)yz = ((x)y)z
```

But `xyz` is *not* equal to, say, `x(yz)`.

And here's a puzzle to start flexing your combinator skills: one of the
combinators in SKI combinator calculus is `I`, which is the identity function.

```
Ix ~> x
```

Try write an expression which functions the same way as `I`, using only the
`BCKW` combinators.
Use the following evaluator to try and figure out how to do it: write an
expression into the box that, when applied to `x`, evaluates to `x`.
You're only allowed to use `B`, `C`, `K`, `W`, and parentheses for this.

<p id="BCKWtoI"></p><script>
small_tester(
  { input_id: "BCKWtoI"
  , output_lines: 3
  , input_width: 5
  , initial_expr: ""
  , vars: "x"
  , expect: "x" 
  , allowed_combos: [Comb.B, Comb.C, Comb.K, Comb.W]
  }
); </script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

<details><summary>Answer</summary>
`CK` followed by any combinator will do the trick.
So `CKB`, `CKK`, `CKC`, etc.

```
I = CKC
```
</details>

# Why Not Simpler Combinators?

Each of the combinators we've defined so far work a little weird: they seem to
skip over their first argument, and work on their second.
Indeed, there is another, equivalent combinator calculus which doesn't have this
peculiarity:

```
Bxyz ~> x(yz)
Axy  ~> y
Mx   ~> xx
Txy  ~> yx
```

`B` stays the same in this calculus, but the rest of the combinators get
switched out for seemingly simpler versions.
`K` goes to `A`^[If you want to look up these combinators elsewhere, this is the only one
you won't be able to find: it's much less common than `K`, and where I have
found it people just call it `K`, so I had to pick a different letter to
distinguish it]:

```
Axy ~> y
Kxy ~> x
```

Which isn't a huge change.
It's the other two where we see the real difference.
`W` has been swapped out for `M`:

```
Wxy ~> xyy
Mx  ~> xx
```

As you can see `W` basically does the same thing as `M`, but while passing
through its first argument.
The difference between `T` and `C` is similar:

```
Cxyz ~> xzy
Txy  ~> yx
```

So, first of all, it is pretty simple to show that `BCKW` contains all of the
`BAMT` combinators.
Try find a way to write `T` using only `BCKW` combinators (hint: you might want
to use your previous answer for writing `I` using `BCKW`).

<p id="BCKWtoT"></p><script>
small_tester(
  { input_id: "BCKWtoT"
  , output_lines: 3
  , input_width: 8
  , initial_expr: ""
  , vars: "xy"
  , expect: "yx"
  , allowed_combos: [Comb.B, Comb.C, Comb.K, Comb.W]
  }
); </script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

<details><summary>Answer</summary>
So in fact all of the changed BAMT combinators can be encoded using BCKW by
putting `I` (or `CKC` or what have you) after the corresponding BCKW combinator.
In other words:
```
T = CI = C(CKC)
A = KI = K(CKC)
M = WI = W(CKC)
```
</details>

It's pretty easy to go from `BCKW` to `BAMT`, then.
However, it's *extremely* difficult to go the other way.
Here, try to write `K` in terms of `BAMT` (this is quite difficult, do not
expect to get it!):

<p id="BAMTtoK"></p><script>
small_tester(
  { input_id: "BAMTtoK"
  , output_lines: 5
  , input_width: 12
  , initial_expr: ""
  , vars: "xy"
  , expect: "x"
  , allowed_combos: [Comb.B, Comb.A, Comb.M, Comb.T]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

<details><summary>Answer</summary>
Either of the following would work:

```
B(TA)(BBT)
B(B(TA)B)T
```
</details>

So this is why we will stick to `BCKW` for the time being: `BAMT` is just too
painful to use.

# Linear Types and Combinators

One of the things BCKW has over SKI is that each combinator represents a
concrete capability.
`K` and `W` especially: without these combinators, we can neither duplicate nor
discard variables.
In other words, `BC` on its own is a *linear* language.
Well, there's one caveat: `BC` doesn't exactly have an equivalent to `I`.
You can get close, but you need to supply at least 3 arguments.
See if you can figure it out:

<p id="BCtoI"></p><script>
small_tester(
  { input_id: "BCtoI"
  , output_lines: 4
  , input_width: 5
  , initial_expr: ""
  , vars: "xyz"
  , expect: "xyz"
  , allowed_combos: [Comb.B, Comb.C]
  }
);
</script><noscript>Turn on JavaScript to allow interactive evaluation</noscript>

<details><summary>Answer</summary>
```
BCC
```
</details>

So usually we add `I`, to get `BCI`.

We can also have an affine language, with `BCK`.

# The Minimal Combinators: S and K

`S` is the only combinator we haven't seen yet.
It's kind of a combination of `B`, `C`, and `W`:

```
Sxyz ~> xz(yz)
```

It does parenthesising, reordering, *and* duplication.


# Encoding Numbers

# Encoding Lambda Terms as Combinators

# Interpreting Combinators

## In Haskell

## In an Imperative Language

# Encoding Combinators

<!-- # Some Other Combinators -->

<!-- We have a good reason for focusing on the `S` and `K` combinators: together, -->
<!-- they're Turing complete, and they're the simplest two combinators which have -->
<!-- that property (I think). -->
<!-- Other combinators are either weirder, or require more than two to get Turing -->
<!-- completeness. -->

<!-- All the same, they are not very intuitive or usable. -->
<!-- We're going to look at two other combinator sets now which are equal in power to -->
<!-- the SK combinators: they have four combinators a piece, though, so they're not -->
<!-- as "simple". -->

<!-- First, we have the `BAMT` combinator set. -->
<!-- I'll give the definition of each first, and then we'll move on to exploring them -->
<!-- a little. -->

<!-- ``` -->
<!-- Bxyz ~> x(yz) -->
<!-- Axy  ~> y -->
<!-- Mx   ~> xx -->
<!-- Txy  ~> yx -->
<!-- ``` -->

<!-- `A` is quite similar to `K`, but it drops is first argument, keeping the -->
<!-- `M` duplicates its argument, and `T` swaps them around. -->
<!-- `B`, like `S`, adds parentheses. -->

<!-- In terms of normal functional code, `B` is composition: it takes two functions -->
<!-- and an argument, and applied those two functions to the argument. -->

<!-- I quite like this combinator set because each combinator is extremely simple in -->
<!-- its function. -->
<!-- Also, each combinator gives a concrete capability to the combinators. -->
<!-- `M`, for instance, allows us to make copies. -->
<!-- If we worked with only the `BAT` combinators, we would know that our interpreter -->
<!-- would always produce an output no larger than its input. -->
<!-- Similarly, `A` allows us to discard information. -->

<!-- A combinator system that didn't include the `A` or `M` combinators would be -->
<!-- *linear*: in fact, some linear logic (and affine logic) systems are based on -->
<!-- this precise symmetry. -->

<!-- So now, let's try use some of them to replicate the `SKI` combinators. -->
<!-- First, `I` (you want to write an expression that, when applied to `x`, returns -->
<!-- `x`): -->

<!-- <p id="BAMTtoI"></p><script> -->
<!-- small_tester( -->
<!--   { input_id: "BAMTtoI" -->
<!--   , output_lines: 2 -->
<!--   , input_width: 3 -->
<!--   , initial_expr: "" -->
<!--   , vars: "x" -->
<!--   , expect: "x"  -->
<!--   , allowed_combos: [Comb.B, Comb.A, Comb.M, Comb.T] -->
<!--   } -->
<!-- ); -->
<!-- </script><noscript>Turn on JavaScript to allow interactive evaluation</noscript> -->

<!-- <details><summary>Answer</summary> -->
<!-- `A` followed by anything (so `AB`, `AT`, `AM`, etc) will give you a combinator -->
<!-- equivalent to `I`. -->
<!-- </details> -->

<!-- That should have been pretty easy. -->
<!-- The next one is *not*: do not expect to be able to get it! -->
<!-- You need to replicate `K`. -->


<!-- That last one was pretty ugly. -->
<!-- `S` is even more horrific still: -->

<!-- ``` -->
<!-- S = B(B(B(T(BM(BBT)))(BBT)))(BB(B(T(BBT))(BBT))) -->
<!-- ``` -->

<!-- You can try out the `BAMT` calculus in the following evaluator, it's loaded up -->
<!-- with the awful equivalence for `S`: -->

<!-- <p id="BAMTtoS"></p><script> -->
<!-- small_repl( -->
<!--   { input_id: "BAMTtoS" -->
<!--   , output_lines: 5 -->
<!--   , input_width: 50 -->
<!--   , initial_expr: "B(B(B(T(BM(BBT)))(BBT)))(BB(B(T(BBT))(BBT)))xyz" -->
<!--   , allowed_combos: [Comb.B, Comb.A, Comb.M, Comb.T] -->
<!--   } -->
<!-- ); -->
<!-- </script><noscript>Turn on JavaScript to allow interactive evaluation</noscript> -->

<!-- # A Usable Combinator Set -->

<!-- So we've seen the theoretically simple `SK` combinators, the simple to -->
<!-- understand (but a nightmare to use) `BAMT` combinators, now we'll introduce a -->
<!-- combinator set which is relatively simple to both understand *and* use: `BCKW`. -->

<!-- ``` -->
<!-- Bxyz ~> x(yz) -->
<!-- Cxyz ~> xzy -->
<!-- Kxy  ~> x -->
<!-- Wxy  ~> xyy -->
<!-- ``` -->

<!-- You can see that it's a little similar to `BAMT`, we have `B`, we have `K` -->
<!-- (which is quite similar to `A`), and the `C` and `W`. -->
<!-- These last two function analogously to `T` and `M`, except they take an extra -->
<!-- argument that they keep in front. -->
<!-- This makes them *far* easier to use. -->
<!-- Here's a repl to try them out. -->
<!-- See if you can figure out the other combinators we've seen so far. -->

<!-- <p id="BCKW"></p><script> -->
<!-- small_repl( -->
<!--   { input_id: "BCKW" -->
<!--   , output_lines: 5 -->
<!--   , initial_expr: "" -->
<!--   , allowed_combos: [Comb.B, Comb.C, Comb.K, Comb.W] -->
<!--   } -->
<!-- ); -->
<!-- </script><noscript>Turn on JavaScript to allow interactive evaluation</noscript> -->


<!-- And here's a puzzle: this is difficult, but doable. -->
<!-- See if you can express `S` using `BCKW` alone. -->

<!-- <p id="BCKWtoS"></p><script> -->
<!-- small_tester( -->
<!--   { input_id: "BCKWtoS" -->
<!--   , output_lines: 5 -->
<!--   , initial_expr: "" -->
<!--   , vars: "xyz" -->
<!--   , expect: "xz(yz)" -->
<!--   , allowed_combos: [Comb.B, Comb.C, Comb.K, Comb.W] -->
<!--   } -->
<!-- ); -->
<!-- </script><noscript>Turn on JavaScript to allow interactive evaluation</noscript> -->

<!-- <details><summary>Answer</summary> -->
<!-- ``` -->
<!-- S = B(BW)(BBC) -->
<!-- ``` -->
<!-- </details> -->
