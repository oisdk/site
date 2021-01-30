---
title: Scheduling Effects
series: Breadth-First Traversals
bibliography: Delay Monad.bib
tags: Haskell
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

We first print `1`, then, after a delay, we print `2`. The `delay`{.haskell}
doesn't make a difference if we just run the whole thing:

```haskell
>>> retract oneThenTwo
1
2
```

But you can see its effect when we use the `interleave`{.haskell} combinator:

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

The genealogy of most coroutine libraries in Haskell seems to trace back to
@blazevic_coroutine_2011 or @kiselyov_iteratees_2012: the implementation I
have been using in these past few examples
([`IterT`](http://hackage.haskell.org/package/free-5.0.2/docs/Control-Monad-Trans-Iter.html))
comes from a slightly different place. Let's take a quick detour to explore it a
little.

# Partiality

In functional programming, there are several constructions for modeling
error-like states: `Maybe`{.haskell} for your nulls, `Either`{.haskell} for your
exceptions. What separates these approaches from the "unsafe" variants
(null pointers, unchecked exceptions) is that we can *prove*, in the type
system, that the error case is handled correctly.

Conspicuously absent from the usual toolbox for modeling partiality is a way to
model *nontermination*. At first glance, it may seem strange to attempt to do so
in Haskell. After all, if I have a function of type:

```haskell
String -> Int
```

I can prove that I won't throw any errors (with `Either`{.haskell}, that is),
because the type `Int`{.haskell} doesn't contain `Left _`{.haskell}. I've also
proved, miraculously, that I won't make any null dereferences, because
`Int`{.haskell} also doesn't contain `Nothing`{.haskell}. I *haven't* proved,
however, that I won't loop infinitely, because (in Haskell), `Int`{.haskell}
absolutely *does* contain $\bot$.

So we're somewhat scuppered. On the other hand, While we can't *prove*
termination in Haskell, we can:

#. Model it.
#. Prove it in something else.

Which is exactly what Venanzio Capretta did in the fascinating (and quite
accessible) talk "Partiality is an effect"
[@capretta_partiality_2004][^later-version]. 

[^later-version]: There is a later, seemingly more formal version of the talk
    available [@capretta_general_2005], but the one from 2004 was a little
    easier for me to understand, and had a lot more Haskell code.

The monad in question looks like this:

```idris
data Iter a
    = Now a
    | Later (Inf (Iter a))
```

We're writing in Idris for the time being, so that we can prove termination and
so on. The "recursive call" to `Iter`{.haskell} is guarded by the
`Inf`{.haskell} type: this turns on a different kind of totality checking in the
compiler. Usually, Idris will prevent you from constructing infinite values. But
that's exactly what we want to do here. Take the little-known function
[`until`{.haskell}](http://hackage.haskell.org/package/base-4.11.1.0/docs/Prelude.html#v:until):

```haskell
until :: (a -> Bool) -> (a -> a) -> a -> a
```

It's clearly not necessarily total, and the totality checker will complain as
such when we try and implement it directly:

```idris
until : (a -> Bool) -> (a -> a) -> a -> a
until p f x = if p x then x else until p f (f x)
```

But we can use `Iter`{.haskell} to model that possible totality:

```idris
until : (a -> Bool) -> (a -> a) -> a -> Iter a
until p f x = if p x then Now x else Later (until p f (f x))
```

Of course, nothing's for free: when we get the ability to construct infinite
values, we lose the ability to consume them.

```idris
run : Iter a -> a
run (Now x) = x
run (Later x) = run x
```


We get an error on the `run`{.haskell} function. However, as you would expect,
we can run *guarded* iteration: iteration up until some finite point.

```idris
runUntil : Nat -> Iter a -> Maybe a
runUntil Z _ = Nothing
runUntil (S n) (Now x) = Just x
runUntil (S n) (Later x) = runUntil n x
```

Making our way back to Haskell, we must first---as is the law---add a type
parameter, and upgrade our humble monad to a monad transformer:

```haskell
newtype IterT m a = IterT { runIterT :: m (Either a (IterT m a)) }

type Iter = IterT Identity
```

The semantic meaning of the extra `m`{.haskell} here is interesting: each layer
adds not just a recursive step, or a single iteration, but a single effect.
Interpreting things in this way gets us back to the original goal:

# Scheduling

The `Later`{.haskell} constructor above can be translated to a `delay`{.haskell}
function on the transformer:

```haskell
delay = IterT . pure . Right
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

# More Coroutines

In the wonderful article Coroutine Pipelines [@blazevic_coroutine_2011], several
different threads on coroutine-like constructions are unified. What I've
demonstrated above isn't yet as powerful as what you might see in a full
coroutine library: ideally, you'd want generators and sinks. As it turns out,
when we look back at the note from `IterT`{.haskell}:

```haskell
IterT ~ FreeT Identity
```

We can get both of those other constructs by swapping out
`Identity`{.haskell}[^adjunction]:

[^adjunction]: Small note: `(,) a` and `(->) a` are adjunct. I wonder if there
    is any implication from this? Certainly, producers and consumers seem
    adjunct, but there's no instance I can find for it in adjunctions.

```haskell
Generator a = FreeT ((,) a)
Sink a = FreeT ((->) a)
```

(`Sink`{.haskell} is usually called an `Iteratee`{.haskell})

This is the fundamental abstraction that underlies things like the pipes library
[@gonzalez_pipes_2018].

# Interleaving

The only missing part from the first coroutine example by now is
`interleave`{.haskell}. In the free library, it has the following signature:

```haskell
interleave :: Monad m => [IterT m a] -> IterT m [a]
```

But we should be able to spot that, really, it's a traversal. And, as a
traversal, it should rely on some underlying `Applicative`{.haskell} instance.
Let's try and come up with one:

```haskell
newtype Parallel m f a = Parallel
    { runParallel :: FreeT m f a
    }

instance (Functor f, Functor m) =>
         Functor (Parallel m f) where
    fmap f = Parallel . FreeT . fmap go . runFreeT . runParallel
      where
        go = bimap f (FreeT . fmap go . runFreeT)

instance (Applicative f, Applicative m) =>
         Applicative (Parallel m f) where
    pure = Parallel . FreeT . pure . Pure
    Parallel fs' <*> Parallel xs' = Parallel (unw fs' xs')
      where
        unw (FreeT fs) (FreeT xs) = FreeT (liftA2 go fs xs)
        go (Pure f) = bimap f (runParallel . fmap f . Parallel)
        go (Free fs) = Free . \case
            Pure x -> fmap (runParallel . fmap ($x) . Parallel) fs
            Free xs -> liftA2 unw fs xs
```

Now, interleave is just `sequenceA`{.haskell}!

# Applicatives, Again

So we can see that there's a "parallel" applicative for both the free monad and
the free applicative. To try and understand this type a little better, we can
leverage our intuition about a much simpler, more familiar setting: lists.
There's an interesting similarity between lists and the free monad: `FreeT ((,)
a)`{.haskell}) looks a lot like "[`ListT`{.haskell} done
right](https://wiki.haskell.org/ListT_done_right)" (so much so, in fact, that
most coroutine libraries provide their own version of it). More concretely, list
also has a famous "parallel" applicative:
[`ZipList`{.haskell}](http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Applicative.html#t:ZipList)!

```haskell
newtype ZipList a
    = ZipList 
    { getZipList :: [a]
    } deriving Functor

instance Applicative ZipList where
  pure = ZipList . repeat
  liftA2 f (ZipList xs) (ZipList ys) = ZipList (zipWith f xs ys)
```

We'll use some of our knowledge about `ZipList`{.haskell} to help us in the next
section.

# Timekeeping

We've seen that efforts to model both coroutines and partiality end up in the
same neighborhood: there's yet another way to get there, which seems (at first)
almost the opposite of the second. It starts with a blog post from Conor McBride
[-@mcbride_time_2009] called "Time flies like an applicative functor".
Curiously, here too breadth-first labeling is the focus. Remember first the
lovely circular solution from @jones_linear-time_1993:

```haskell
data Tree a = Leaf | Node a (Tree a) (Tree a)

relabel :: Tree x -> [[a]] -> (Tree a, [[a]])
relabel Leaf xss = (Leaf,xss)
relabel (Node _ l r) ((x:xs):xss0) =
  let (l',xss1) = relabel l xss0
      (r',xss2) = relabel r xss1
  in (Node x l' r',xs:xss2)
  
bflabel :: Tree x -> [a] -> Tree a
bflabel tr xs = u
  where
    (u,xss) = relabel tr (xs:xss)
```

As lovely as it is, spare a thought for the poor totality checker: it's hard to
imagine how it would even *start* to show that something so lazy and circular
would terminate. `IterT`{.haskell} won't help us here, either: it can help us
express programs that *might* diverge, not weird-looking ones that definitely
won't. 

The solution presented is a type (`De`{.haskell}) which has a limited set of
combinators: a fixpoint (`fix :: (De x -> x) -> x`{.haskell}), and an
applicative instance. As long as all problematic recursive calls are instead
expressed using those combinators, the termination checker should be satisfied.

`De`{.haskell} can be thought of as a "delay" wrapper. Values of type `De
a`{.haskell} are one step in the future, `De (De a)`{.haskell} are two, and so
on. This idea was later expanded upon in @atkey_how_2011 and
@atkey_productive_2013 to *clock variables*. Instead of types with a delay,
types are tagged with how much more time they have (something like "fuel" in the
Idris sense, maybe). So a value of type $a^\mathsf{K}$ is tagged with time
$\mathsf{K}$, effectively meaning "I have $\mathsf{K}$ productive steps left
before I diverge". "Productive steps" will mean something different for every
data type: for lists, it could mean that it can produce up until the
$\mathsf{K}$th cons-cell. In the paper [@atkey_productive_2013] this is fleshed
out a little more, with fixpoint combinators and so on. As a concrete example,
take the type of the cons operator on streams:

\begin{equation}
\text{Cons} : \text{a}
\rightarrow \text{Stream a}^\mathsf{K}
\rightarrow \text{Stream a}^{\mathsf{K}+1}
\end{equation}

It increments the clock on the type, saying that it has one more productive step
than it did before. This is kind of the opposite of a "delay": previously, the
scheduling types have meant "this is available $\mathsf{K}$ number of steps in the
future" rather than "this is available for another $\mathsf{K}$ steps". We can
still describe delays in this system, though, using the $\rhd^\mathsf{K}$
notation:

\begin{equation}
\text{Cons} : \text{a}
\rightarrow \rhd^\mathsf{K}\text{Stream a}
\rightarrow \text{Stream a}
\end{equation}

Let's first try express some of this in the free monad:

```haskell
data K = Z | S K

data Delay :: K -> (Type -> Type) -> (Type -> Type) -> Type -> Type where
  Now   :: a -> Delay n f m a
  Later :: f (DelayT n f m a) -> Delay (S n) f m a

instance (Functor f, Functor m) => Functor (Delay n f m) where
  fmap f (Now x) = Now (f x)
  fmap f (Later xs) = Later (fmap (fmap f) xs)

newtype DelayT n f m a = DelayT { runDelayT :: m (Delay n f m a) }

instance (Functor f, Functor m) =>
         Functor (DelayT n f m) where
    fmap f = DelayT . fmap (fmap f) . runDelayT
```

We can straight away express one of the combinators from the paper,
`force`{.haskell}:

```haskell
force :: Functor m => (∀ k. DelayT k f m a) -> m a
force (DelayT xs) = fmap f xs
  where
    f :: Delay Z f m a -> a
    f (Now x) = x
```

Similar trick to
[`runST`{.haskell}](http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Monad-ST.html#v:runST)
here: if the type is delayed however long we want it to be, then it mustn't
really be delayed at all.

Next, remember that we have types for streams (generators) from
the `IterT`{.haskell} monad:

```haskell
type Stream n a = DelayT n ((,) a)
```

And cons does indeed have the right type:

```haskell
cons :: Applicative m => a -> Stream n a m b -> Stream (S n) a m b
cons x xs = DelayT (pure (Later (x,xs)))
```

We also get an applicative:

```haskell
instance (Applicative f, Applicative m) =>
         Applicative (DelayT n f m) where
    pure = DelayT . pure . Now
    DelayT fs' <*> DelayT xs' = DelayT (liftA2 go fs' xs')
      where
        go :: ∀ k a b. Delay k f m (a -> b) -> Delay k f m a -> Delay k f m b
        go (Now f) = fmap f
        go (Later fs) = Later . \case
            Now x -> fmap (fmap ($x)) fs
            Later xs -> liftA2 (<*>) fs xs
```

Now, I'm not sure how much this stuff actually corresponds to the paper, but
what caught my eye is the statement that `De`{.haskell} is a classic
"applicative-not-monad": just like `ZipList`{.haskell}. However, under the
analogy that the free monad is listy, and the parallel construction is
ziplist-y, what we have in the `DelayT`{.haskell} is the equivalent of a
length-indexed list. These have an applicative instance similar to ziplists: but
they also have a monad. Can we apply the same trick here?

# Future Posts

There's a lot of fascinating stuff out there---about clock variables,
especially---that I hope to get a chance to learn about once I get a chance.
What I'm particularly interested to follow up on includes:

#. Comonads and their relationship to these constructions. Streams are naturally
   expressed as comonads, could they be used as a basis on which to build a similar
   "delay" mechanism?
#. I'd love to explore more efficient implementations like the ones in @spivey_faster_2017.
#. I'm interested to see the relationship between these types, power series, and
   algebras for combinatorial search [@spivey_algebras_2009].

# References
