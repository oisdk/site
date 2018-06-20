---
title: Scheduling Effects
series: Breadth-First Traversals
bibliography: Delay Monad.bib
---

After the [last
post](2018-06-03-breadth-first-traversals-in-too-much-detail.html), Noah
Easterly pointed me to their [tree-traversals
library](https://hackage.haskell.org/package/tree-traversals), and in particular
the
[`Phases`{.haskell}](https://hackage.haskell.org/package/tree-traversals-0.1.0.0/docs/Control-Applicative-Phases.html#t:Phases)
applicative transformer. It allows you to batch applicative effects to be run
together: for the breadth-first traversal, we can batch the effects from each
level together, giving us a lovely short solution to the problem.

```haskell
breadthFirst c = runPhasesForwards . go
  where
    go (x:<xs) = liftA2 (:<) (now (c x)) (delay (traverse go xs))
```

In my efforts to speed this implementation up, I came across a wide and
interesting literature on scheduling effects, which I'll go through a little
here.

# Coroutines

The first thing that jumps to mind, for me, when I think of "scheduling" is
coroutines. These are constructs that let you finely control the order of
execution of effects. They're well explored in Haskell by now, and most
libraries will let you do something like the following:

```haskell
oneThenTwo = do
  liftIO $ print 1
  delay $ liftIO $ print 2
 ```

We first print `1`, then, after a delay, we print `2`. While the scheduling
isn't visible when we run the above expression:

```haskell
>>> retract oneThenTwo
1
2
```

We can *interleave* the effects of these expressions: here the scheduling
becomes apparent:

 ```haskell
>>> retract $ interleave (replicate 3 oneThenTwo)
1
1
1
2
2
2
```

Hopefully you can see how useful this might be, and the similarity to the
`Phases`{.haskell} construction.

The genealogy of most coroutine-like-things in Haskell traces back to iteratees 

Before I dive into the implementation (these past few examples used the
[`IterT`](http://hackage.haskell.org/package/free-5.0.2/docs/Control-Monad-Trans-Iter.html)
monad transformer), let's take a brief detour. While the genealogy of most
coroutine libraries in Haskell seems to trace back to @blazevic_coroutine_2011
or @kiselyov_iteratees_2012-1, this particular implementation comes from a
different place.

# Partiality

In functional programming, there are several constructions for modeling
error-like states: null references with `Maybe`{.haskell}, exceptions with
`Either`{.haskell}. What separates these approaches from the "unsafe" variants
(null pointers, unchecked exceptions) is that we can *prove*, in the type
system, that the error case is handled correctly.

Conspicuously absent from the usual toolbox for modeling partiality is a way to
model *nontermination*. At first blush, it may seem strange to attempt to do so
in Haskell. After all, if I have a function of type:

```haskell
String -> Int
```

The type system can prove that I won't throw an errors (with `Either`{.haskell},
that is), because the type `Int`{.haskell} doesn't contain `Left _`{.haskell}.
I've also proved, miraculously, that I won't make any null dereferences, because
`Int`{.haskell} also doesn't contain `Nothing`{.haskell}. I *haven't* proved,
however, that I won't loop infinitely, because (in Haskell), `Int`{.haskell}
absolutely *does* contain $\bot$.

While we can't prove termination in Haskell, we can:

#. Model it.
#. Prove it in something else.

Which is exactly what Venanzio Capretta did in the fascinating (and quite
accessible) talk "Partiality is an effect" [@capretta_partiality_2005].

The monad to encapsulate nontermination is as follows:

```haskell
newtype IterT m a = IterT { runIterT :: m (Either a (IterT m a)) }
```

This can be thought of as a (possibly infinite) layering of `m` over a final
value `a`{.haskell}. Every layer can be thought of as a "step" of recursion, or
a single iteration of a loop. So, while we can *write* a function that runs the
whole thing:

```haskell
retract :: Monad m => IterT m a -> m a
retract m = runIterT m >>= either pure retract
```

We know it's not total. We could, however, run it with an iteration limit:

```haskell
data Nat = Z | S !Nat

guardedRetract :: Monad m => Nat -> IterT m a -> m (Maybe a)
guardedRetract Z _ = pure Nothing
guardedRetract (S n) m = runIterT m >>= either (pure . Just) (guardedRetract n)
```

And this function is total, as you would expect. This gives you all the
vocabulary you'd imagine you should have when talking about nontermination, in a
principled way.

# Scheduling

Aside from modeling nontermination, the `IterT`{.haskell} monad can also model
scheduling: it provides a `delay`{.haskell} function, and
`interleave`{.haskell}, demonstrated above. `delay`{.haskell}, from the
perspective of termination, adds one extra step to the computation. To create an
infinite loop, we just delay forever:

```haskell
never = delay never
```

And using this again, we can write the following incredibly short definition for
`unfoldTreeM_BF`{.haskell}:

```haskell
unfoldTreeM_BF :: Monad m => (b -> m (a, [b])) -> b -> m (Tree a)
unfoldTreeM_BF f = retract . go
  where
    go b = do
      (x,xs) <- lift (f b)
      fmap (Node x) (interleave (map (delay . go) xs))
```

# Applicative

It would be nice to bring this back to traversals, but alas,
`IterT`{.haskell} is pretty monad-centric. What's more, if it's analogous to
`Phases`{.haskell} it certainly doesn't look like it:

```haskell
data Phases f a where
  Lift :: f a -> Phases f a
  (:<*>) :: f (a -> b) -> Phases f a -> Phases f b
```

However, in the documentation for
[`IterT`{.haskell}](http://hackage.haskell.org/package/free-5.0.2/docs/Control-Monad-Trans-Iter.html#t:IterT),
there's the following little note:

```haskell
IterT ~ FreeT Identity
```

Where `FreeT`{.haskell} is the [free monad
transformer](http://hackage.haskell.org/package/free-5.0.2/docs/Control-Monad-Trans-Free.html).
This seems to strongly hint that we could get the same thing for applicatives
with
[`ApT`{.haskell}](http://hackage.haskell.org/package/free-5.0.2/docs/Control-Applicative-Trans-Free.html).
Let's try it:

```haskell
newtype Phases f a = Phases
    { runPhases :: ApT Identity f a
    } deriving Functor
```

The `Applicative`{.haskell} instance is a little hairy, but it *seems* correct:

<details>
<summary>
Applicative Instance
</summary>
```haskell
instance Applicative f =>
         Applicative (Phases f) where
    pure = Phases . pure
    liftA2 f' (Phases (ApT xs')) (Phases (ApT ys')) =
        Phases (ApT (liftA2 (go f') xs' ys'))
      where
        go
            :: ∀ a b c.
               (a -> b -> c)
            -> ApF Identity f a
            -> ApF Identity f b
            -> ApF Identity f c
        go f (Pure x) ys = fmap (f x) ys
        go f xs (Pure y) = fmap (`f` y) xs
        go f (Ap x (ApT xs)) (Ap y (ApT ys)) =
            Ap
                (liftA2 (,) x y)
                (ApT (liftA2 (go (\xx yy -> uncurry f . (xx *** yy))) xs ys))
```
</details>

(on a side note: thank *goodness* for `liftA2`{.haskell} finally getting into
`Applicative`{.haskell})

And we get all the normal combinators:

```haskell
delay :: Applicative f => Phases f a -> Phases f a
delay = Phases . ApT . pure . Ap (pure ()) . fmap const . runPhases

lift :: Functor f => f a -> Phases f a
lift = Phases . liftApO
```

The issue comes with running the thing at the end: `Monad`{.haskell} creeps back
in.

```haskell
retract :: Monad f => Phases f a -> f a
retract = fmap (runIdentity . retractAp) . joinApT . runPhases
```

Because the effects are all layered on top of each other, you need to flatten
them out at the end, which requires `join`{.haskell}. Mind you, it does work:
it's just not as general as it could be.

All's not lost, though. Turns out, we never needed the transformer in the first
place: we could just define the different applicative instance straight off.

```haskell
newtype Phases f a = Phases
    { runPhases :: Ap f a
    } deriving Functor

instance Applicative f =>
         Applicative (Phases f) where
    pure = Phases . Pure
    liftA2 f' (Phases xs') (Phases ys') = Phases (go f' xs' ys')
      where
        go :: ∀ a b c.
              (a -> b -> c)
           -> Ap f a
           -> Ap f b
           -> Ap f c
        go f (Pure x) ys = fmap (f x) ys
        go f xs (Pure y) = fmap (`f` y) xs
        go f (Ap x xs) (Ap y ys) =
            Ap
                (liftA2 (,) x y)
                (go (\xx yy -> uncurry f . (xx *** yy)) xs ys)

delay :: Applicative f => Phases f a -> Phases f a
delay = Phases . Ap (pure ()) . fmap const . runPhases

retract :: Applicative f => Phases f a -> f a
retract = retractAp . runPhases

lift :: f a -> Phases f a
lift = Phases . liftAp
```

# ListT
