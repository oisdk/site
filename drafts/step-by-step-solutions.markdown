---
title: Step-By-Step Solutions, Formally
tags: Agda
---

This post today is going to be about a small bit from my undergraduate thesis:
how to write a formal, verified program that automates proofs about arithmetic
expressions, and also *explains* the proofs in a step-by-step way.
Basically it's what the internals of Wolfram Alpha might look like if it were
written in Agda.

# The Goal: Step-By-Step Solutions

For those who don't know [Wolfram Alpha](https://www.wolframalpha.com/) is a
"computational knowledge engine", which as far as I can tell is pseudoscientific
marketing-speak for a scientific search engine geared towards natural-language
processing.
Like ask Jeeves but for secondary-school science and mathematics.

Hyperbolic marketing copy aside, the actual stuff that Wolfram Alpha does is
pretty useful and interesting.
There are several different features, but the one I'm interested in is the
step-by-step solutions.
If you put in something like $x^2 + 5x + 6 = 0$ it will [give the following steps
to solve](https://www.wolframalpha.com/input/?i=x%5E2+%2B+5x+%2B+6+%3D+0&lk=3):

#. Solve for $x$ over the real numbers:

   $x^2 + 5x + 6 = 0$

#. The left hand side factors into a product  with two terms:

   $(x + 2)(x + 3) = 0$

#. Split into two equations:

   $x + 2 = 0$ or $x + 3 = 0$

#. Subtract 2 from both sides:

   $x = -2$ or $x + 3 = 0$

#. Subtract 3 from both sides:

   $x = -2$ or $x = -3$
   
To me, this is extremely cool and useful.
I haven't really looked in to the rest of Wolfram Alpha a lot, but this one
small bit in particular seems like it would be hugely useful for junior cert
maths.

I am aware that there are similar, perhaps more heavy-duty, systems for computer
algebra out there (Maple, SymPy, etc), but I'm not really aware of much else in
the way of this step-by-step thing.
So when I was writing my undergrad thesis, I thought this might be a nice topic
to use as an example use of the solver I had written.
To do this, I had to figure out what the "theory" of step-by-step solutions was,
which turned out to be a kind of interesting demonstration of constructive
maths.

# The Solver (Briefly)

The solver is pretty simple: given an equality between two expressions, the
solver will attempt to prove that the expressions are equal.
It's pretty powerful and general (I haven't run across any equalities in the
integers, for instance, which are equal but the solver can't handle), and it
works like this:

```agda
lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
lemma = solve NatRing
```

The thing we want to solve is the expression on the first line: we call the
solver with the ring for the natural numbers^[Well technically not a *ring*, but
what's called an *almost-ring*. We need this different algebra because, while a
lot of the algorithms are described in terms of rings, a lot of the useful
arithmetic types we might be interested in don't have negation (like the natural
numbers). The axioms of the almost-ring algebra allow to be defined as the
identity (i.e. they don't require it to be the inverse for +), but still allows
expressions to be solved efficiently.].
The solver uses reflection and some other fancy Agda features to make the
interface nice and easy to use.
If you're interested in reading more about it, there is of course the [thesis
itself](2019-07-14-bsc-thesis.html).

# Setoid Hell

One of the major headaches involved in writing a solver like this is known as
"setoid hell".
Because we want the solver to be as general as possible, we don't want to
require the equalities to be "actual" equalities: instead they can be
*equivalences*, i.e. any binary relation with transitivity, reflexivity, and
symmetry (and a type with one of these equivalences is called a setoid).

While this is great for a user, for an implementer it's pretty awful.
Because we don't get to work with actual equalities, we can't pattern-match on a
proof of equality, or substitute one equal type with another, or use congruence
in proofs.
Basically, several of the normal techniques one might use to write equality
proofs aren't possible with equivalences, making proofs about them really
complex and annoying.

Luckily, some of this is obfuscated (a little) by Cubical Agda: one of the major
reasons one might need setoids is for *quotients*.
These are types that are formed by putting some equivalence relation on another
type: for instance in Haskell we represent sets and maps with balanced binary
trees.
This representation, while efficient, isn't perfect, however, as two of the same
sets can be represented by different trees (i.e. where one might just be after a
rebalancing and another might be just before one).
So we treat these trees as *quotients* in Haskell: we ignore the different
actual tree structures different trees, and say that two trees with the same
elements are the "same".
While this is all pretend quotients (i.e. the type system has no notion of
quotients in Haskell, and we don't have any way to check formally that we really
are ignoring the invariants associated with the quotienting operation), Cubical
Agda (and HoTT generally) allows us to do it.

There are other uses for setoids, however, and one of those uses is what I
leveraged to get step-by-step solutions out of the solver.

# It's About the Journey, not the Destination

Often in constructive mathematics we talk about mathematical "objects".
We say that we can manipulate and use proofs like objects in the same way that
we manipulate and use---say---data structures, or numbers.

One of the things that it is useful to look at as an "object" is the equality
proofs that we generate in the solver.
In the example above we generated an actual *value* which corresponded to the
proposition $x + y \times 1 + 3 = 2 + 1 + y + x$: maybe there's something in
that from which we can generate a step-by-step explanation?

Well, not quite.
The equality type in Agda is the most subtle and complex of the primitive
types for sure: but it doesn't contain any information.
All equality proofs (on the same type) are equal: they're *propositions*.
We'll ignore HoTT and CuTT for now (even thought equalities there are not
necessarily propositions, they have to be over special types in order for them
to be non propositions).

But we're not working with equalities: we're working with *equivalences*. 
And these equivalences only 


# What if you wanted to implement this yourself?
