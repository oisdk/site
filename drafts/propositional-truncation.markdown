---
title: "Propositional Truncation: It's not what you think!"
tags: Agda
---

One of the big differences between "constructive" and classical mathematics is
the behaviour of existentials.

The other day there was a discussion on Twitter about propositional truncation
and decidable equality: I actually made a mistake regarding the uniqueness of
equality proofs (which [Amélia caught and
corrected](https://twitter.com/plt_amy/status/1466605904086937607?s=20)), but
the discussion reminded me of one of the more interesting proofs I came across
when doing my Master's thesis, concerning a proof of the following fact:

```agda
∀ {A} → isProp (∀ (x y : A) → (x ≡ y) ⊎ (x ≢ y))
```

This type says that any function which computes decidable equality on some type
(i.e. it returns whether or not two elements of the type are equal) is itself a
proposition.
A proposition is some type for which there is at most one inhabitant.

When comparing classical and constructive mathematics, we often reach for
propositions as a way to illustrate some of the difference.
Classical mathematics, so the story goes, is not concerned with the "content" of
proofs; only if they are true or false.

As an example, take the proposition that "there is a prime number bigger than
100".
To prove this, you could
provide a number, prove that it's bigger than 100, and then prove that it's
prime.
You could alternatively show that there being finitely many primes implies
another absurdity, and therefore there must be at least one hundred, and by
right some of those must be *bigger* than one hundred.

In classical mathematics all of these proofs basically prove the same thing, as
far as the person asking is concerned.
Constructively, though, we can often tell the difference between those two
proofs: in fact, we can tell the difference between a proof that "there are
primes bigger than 100 (because 101 is prime)" and "there are primes bigger than
100 (because 103 is prime)".
It all depends on the *type* of the proof in question.
For this proposition, the simplest and most obvious type for this particular
proof is the following:

```agda
∃ n × (n > 100) × isPrime n
```

In computer-science terms, this is a tuple, where the first component is a
natural number, the second is a proof that it's bigger than 100, and the last is
a proof that it's prime.
Again, in computer science terms, we can retrieve what number was used in the
proof by simply extracting the first component of the tuple.

So: the difference between the two formalisms is simple.
Constructive mathematics can take out the *content* of proofs, because it can
tell the difference between these different proofs.

Except that that's not true at all!

