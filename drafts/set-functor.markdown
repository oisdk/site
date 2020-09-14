---
title: Sets are Functors (clearing up a little confusion)
tags: Haskell
---

So I recently saw [this
tweet](https://twitter.com/cdsmithus/status/1304484063026216960) from Chris
Smith:

> In Haskell, Set a is a covariant functor, but (a -> Bool) is a contravariant
> functor.  But, aside from finiteness, they should mean approximately the same
> thing.  Weird, huh?
>
> Chris Smith, [\@cdsmithus](https://twitter.com/cdsmithus)
>
> Sep 11, 2020

And it reminded me of a particular point of confusion I personally had with
regards to sets and functors a while ago: I had long thought that sets couldn't
form functors because they broke the composition law.
This confusion had stemmed from a few comments on forums and stackoverflow which
were a pretty misleading (some comments were technically correct but quite
misleading, others did actually contain factual errors), and it was only much
later that I realised my mistake.

As it happens, this mistake seems to be pretty pervasive amongst Haskellers
online, so I thought I would write this post to try and clear up the story a
little.

To lay out exactly where I went wrong, my misconception came about like this:
at the point where I had a decent understanding of Functors and Monads and so
on, I realised that `Set` (in `Data.Set`) has some of the required functions to
be a member of those classes.
I also noticed that it *wasn't* a member of those classes, so I tried to define
an instance, but I quickly realised that that wasn't possible, because of the
`Ord` constraint that `Set` has on functions like `map`.

Later, I saw (on reddit or something I think) that apparently even if we had a
`Functor` class which allowed constraints like `Ord`, `Set` wouldn't have a
valid instance, because it breaks the composition law:

```haskell
fmap f . fmap g = fmap (f . g)
```

I chalked that up as in interesting fact about sets, and left it there.

But this is incorrect! 
Well, maybe not incorrect, but extremely misleading.
`Set` can possibly break that Functor law, but only if the type it's defined
over has a bonkers `Eq` instance.
If the `Eq` instance is in any way sensible `Set` is a fully law-abiding
*Monad*, never mind a Functor!
Now, as it happens, `Eq` in Haskell is a class without any laws: instances need
not represent actual equivalence relations, and they need not respect
substitution.
So you might say that we shouldn't rely on convention regarding a class that
isn't specified in any of its actual laws: however, if we're to say that, then
practically *every* class implemented by `Set` breaks the laws!
It's not a lawful monoid, or semigroup, and it fully breaks the vast majority of
guarantees made in `Data.Set`.

So, in summary, `Set` *could* be a perfectly normal Functor (in the same sense
that `Set` is a `Monoid`) if we had a Functor class which allowed for
constraints; the issue with the `Eq` class is a technicality which we ignore in
far more cases than just `Set`.
If you, like me of a few years ago, were under the impression that sets couldn't
be functors for some fundamental reason, that's all you really need to know.
For the rest of this post I'll dive into some of the details on the mathematical
structure that `Data.Set` represents, and some of the interesting and confusing
subtleties that it entails.
