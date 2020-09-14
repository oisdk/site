---
title: Sets are Functors (clearing up a little confusion)
tags: Haskell
---

There is some confusion floating around among Haskellers that
sets---specifically, the sets that Data.Set approximates---aren't functors.
This misconception is based on a "technically true" observation about the `Eq`
class in Haskell which some people (including myself for quite a while) draw
overly-strong conclusions from.
In this post I'll go through (and correct) the misconception as clearly as I
can, and then I'll dive into some more interesting details about sets in type
theory.

# Clearing Up the Confusion

So, first things first: let's try write a Functor instance for `Set`, and see
where we go wrong.
What we need is an implementation of `fmap`:

```haskell
fmap :: (a -> b) -> Set a -> Set b
```

In
[`Data.Set`](hackage.haskell.org/package/containers-0.6.3.1/docs/Data-Set.html)
we do have the
[`map`](http://hackage.haskell.org/package/containers-0.6.3.1/docs/Data-Set.html#v:map) function:

```haskell
map :: Ord b => (a -> b) -> Set a -> Set b
```

But, as you can see, the type signature of the functions are different.
Functor requires us to `fmap` *any* function from `a` to `b`, whereas
`Data.Set`'s `map` needs `b` to be an instance of `Ord`.

For a lot of people that might be the end of the story.
`Data.Set` simply doesn't support the required function, so it's not a Functor.
But we know that the Functor class in Haskell is really just an approximation of
*actual* Functors: in fact it's really an approximation of endofunctors in the
category of Haskell types.
It turns out that, theoretically, one could have a different kind of class which
allowed for endofunctors in---say---all Haskell types with an `Ord` instance.
Or in fact, with constraint kinds, we could have a functor class for all
class-based subsets of Haskell types.
We might define it like so:

```haskell
class Functor f where
  type Domain f (a :: *) :: Constraint
  type Domain f a = ()
  
  fmap :: (Domain f a, Domain f b) => (a -> b) -> f a -> f b
```

And we could have instances like this:

```haskell
instance Functor [] where
  fmap = map
  
instance Functor Set where
  type Domain Set a = Ord a
  fmap = Set.map
```

If that last bit went over your head, don't worry: the point I'm trying to show
is that the type defined in Data.Set could well be a Functor if the Functor
class in Haskell had been defined a little differently.
You don't need to know what constraint kinds are or anything like that to
understand the rest of this post.

So Data.Set *could* be a Functor, in a perfect world, but we're denied that
opportunity because of a slightly simpler Functor class.
Except, according to some sporadic comments on reddit and other places, even
with the above class Data.Set can't form a law-abiding instance.

The crux of the issue is the following law:

```haskell
fmap f . fmap g = fmap (f . g)
```

If we define the following type:

```haskell
newtype Prop a = Prop { runProp :: a }

instance Eq (Prop a) where
  _ == _ = True
  
instance Ord (Prop a) where
  compare _ _ = EQ
```

Then the law can be broken like so:

```haskell
>>> fmap (runProp . Prop)      (Set.fromList [1,2,3])
fromList [1,2,3]

>>> (fmap runProp . fmap Prop) (Set.fromList [1,2,3])
fromList [3]
```

And the law has been broken!
Of course, it relied on an absolutely bonkers `Eq` instance, but that's fine,
because *the `Eq` class in Haskell has no laws*.
So, with totally law-abiding instances all around, the Functor instance breaks,
meaning that Data.Set must not be able to be a Functor.

This is the "technically true" observation.
The misconception (which I and a few others believed for a period) is that this
means that Sets can't be functors for some fundamental mathematical reason,
rather than a weird quirk of the `Eq` class not having any laws.
To be absolutely clear: if the *customary* laws for `Eq` are followed (described
in the [documentation for the
class](http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Eq.html#t:Eq)),
then Data.Set forms a totally reasonable Functor.

I also do think it's a little misleading to focus on the Functor class: indeed,
if wonky Eq instances like the one above are allowed, the *majority* of
guarantees made in Data.Set are broken.

So, in summary: the reason that Data.Set can't form a functor in Haskell is
precisely because of the `Ord` constraint, which isn't allowed in the Functor
class.
If it was, then sets would form a perfectly reasonable functor instance: the
fact that we're relying on laws from Eq that aren't technically required is more
of a historical wrinkle than a fundamental flaw.
Besides, if those laws are violated the whole Data.Set module becomes
practically useless anyways.

The rest of this post will be about some of the more theoretical and subtle
aspects of Data.Set.
That module is a Haskell representation of some ideal mathematical object: it
turns out that this object is interesting in its own right, and with a little
modern type theory we can actually define it precisely and see how it behaves.

# The Theory


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


-------

(previous work:)

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
