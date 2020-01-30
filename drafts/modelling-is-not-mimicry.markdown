---
title: Modelling is not Mimicry
---

I just read Alexis King's excellent [blog
post](https://lexi-lambda.github.io/blog/2020/01/19/no-dynamic-type-systems-are-not-inherently-more-open/)
on some of the difference between static and dynamic type systems, and it got me
thinking again about the arguments we have about programming languages.

Though I've [written about this
before](2019-10-02-what-is-good-about-haskell.html), I don't really like to
weigh in on this debate if I can help it.
The sad fact is that discourse on the topic is usually extremely unscientific.
What's in contention is usually pretty quantifiable ("language x is less
bug-prone than language y", "language x tends to take less developer time to
accomplish the same tasks as language y", "language x tends to produce faster
programs than language y"), but actual proper studies into those questions are
few and far between (though not absent).
More worryingly, programmers as a whole seem to be unaware of such studies.

As a result, I try to be very careful to not make claims about the efficacy or
otherwise of any one programming language.
To be honest, it doesn't really interest me, but more importantly I have not
done the necessary work in examining the evidence to make any kind of claim one
way or the other.

That said, there are some isolated arguments which we can make or refute without
making empirical claims.
Alexis King's post above is one such example, as is the one I want to talk about
here.
I want to talk about one specific argument that I occasionally see in online
forums regarding why you should use a dynamic/imperative/object-oriented
language over a static/functional one.
To stress: I do not know whether you should switch to a statically-typed
language at your job, or whether Haskell is less buggy than PHP.
I just want to push back against this specific argument.

With that preamble out of the way, then, let's get to what I actually wanted to
talk about.

# "The Real World is Imperative"

You may have heard this line, or something like it, before.
"Sure, Haskell is nice and pure and mathematical. But guess what, bucko? This is
the real world, and here in the real world things get messy."

The implicit argument here is that some features of mainstream object-oriented
languages, like mutability, reflect similar "features" in the real world, making
mainstream OO languages better at *modelling* the real world.
I think this is incorrect.
To me, it reads like "the real world is messy, so our programming languages
should be messy too!"

The core issue is to do with mimicry versus modelling.
The two things are often conflated, especially in software engineering and
computer science courses.
Stop me if you've heard this before: "the `cat` object inherits from the
`animal` object", or "we have a `user` object, which is a subclass of `person`
object. `employee` is another subclass of the `person` object".

These examples "model" the world by building a small copy of it inside a
computer's memory.
In that sense, mutability is very helpful, as are most of the features of
object-oriented languages.
But it's *not the only way to model something*.
I'm going to work through a small example of what I mean here to illustrate the
point.

# The Employee Object

I want you to imagine a hard-nosed, Real World company, with real men being real
engineers etc.
Such a place must have a state-of-the-art Object Oriented class hierarchy
somewhere in their codebase with a no-nonsense `Employee` class somewhere near
the bottom.
This object has a number of fields, but the one we're interested for now is the
`age` field, which is an `int`.

One day a bigshot object oriented programmer (Straw Manning, we'll call him, for
no particular reason) challenges the upstart Haskeller to model the employee
object---just the age field---in Haskell.

At first it's not so difficult: Haskell also has data types with fields, and
`Int`s, and so on. 
So far, so good: functional programming can "model" the real world.

But wait!
The object-oriented programmer points out that while yes, Haskell can represent
the `age` field, they can't *mutate* it.
This is a crucial aspect of modelling!
Age changes every year, after all.

So the Haskeller returns to their Haskell code begrudgingly, but remembers that
Haskell has a wonderful thing called Monads, of which the State monad is an
esteemed member.
Smugly, they say they have figured out a way to do mutation in Haskell, with
nothing more than a few `>>=`s and `pure`s.

The object oriented programmer, not defeated, points out that the OO code
changes the `age` field every year, on the employee's birthday.
By right, the Haskell code should do the same.
The Haskeller is sweating a little now, since they remember that
"time-sensitivity" is another Monad.
"It's not a problem", they say to themselves, "as we can stack the two Monads on
top of each other, and use them nearly seamlessly".
Twenty or so lines of mtl boilerplate later and they present a Haskell program
that runs indefinitely, mutating an `age` field on an employee's birthday once a
year.

The object-oriented programmer is a little worried at this point, after
watching a frustrated Haskeller mutter "Monads can't compose? Or Monads don't
*want* to compose..." under their breath for a few minutes.
Their program does indeed work, though, although it is getting quite long.
Offhand, the OO programmer mentions that we've only actually managed to deal
with *one* employee, when of course we would need to deal with many.

"Ok. Ok! Ok. No problem.
We just need to wrap that `Employee` type in a list, and we're fine.
Hey! Look! There's even a thing in `lens` called `Zoom` which will let us use
our old state-modifying code again! I think!"

Several minutes later, the object-oriented programmer asks apprehensively if
everything's ok, after seeing the Haskeller laugh maniacally at the `+=` operator
finally typechecking.

"Fine! Fine."

The object oriented programmer sheepishly says "ok, well---and you really don't
need to do this part, I'm sure your code is great---but, technically, my
solution runs in the background, concurrent to the rest of my code."

"Ha! No need for worry there: concurrency is where Haskell shines!"

"Sure," they think, "I haven't actually *written* much concurrent code, but it
can't be too difficult.
Wait---if I want to update the age field, and have it accessible outside of the
thread we update it in, can I even *use* the state monad?
Oh no.
Oh god."

"What... What's an MVar?"

Several months later, after moving to a new company, the Haskeller (now a proud
Gopher) remembers the trauma of trying to implement Real World Solutions code in
Haskell.
Shuddering, they idly look at how `age` is handled in the current code base.
After not being able to find the field, they ask another programmer about it.

"Huh? Age? No, we don't store that as a field. We just store the date of birth."

# Haskell is Bad at Mimicry

Listen, I know very few people would write a mutable `age` field in an
`employee` object (although I have seen it in educational material).
The point is not that "the object-oriented solution is bad".
The point is that *mimicry* is not inherently a good way to *model*.
When someone says "well, Haskell is immutable, but the real world is mutable!"
the answer is "So?". 
The *correct* way to model someone's age is to store its immutable form: their
date of birth (yes, I know, DOB is not actually immutable).

You see this argument pop up all the time in programming contexts.
"*Computers* are imperative". So? Why should our programming languages be?

I'm not saying that there are no good arguments for object-oriented programming
over functional programming, I'm just saying that this isn't one of them.
Mimicry and modelling are not the same thing, and a model's usefulness should
not be judged on how similar it looks to the thing it's modelling.
