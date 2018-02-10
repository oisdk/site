---
title: Getting Monads From Applicatives
tags: Haskell, applicative
bibliography: Monadic List Functions.bib
---

In the last post, I went through some of the monadic generalisations of common list functions. We saw how if you use lists (nondeterminism) as the monad, you could generate several useful functions from simpler ones. We also noticed that, while these were "monadic" generalisations, they often only *required* an underlying `Applicative`{.haskell} constraint. The one function which was resistent to this applicative downgrading was sort. Let's look at why, with a simple ([not](http://augustss.blogspot.ie/2007/08/quicksort-in-haskell-quicksort-is.html)) quicksort:

```haskell
sort :: Ord a => [a] -> [a]
sort [] = []
sort (x:xs) = sort le ++ [x] ++ sort gt
  where
    (le,gt) = partition (<=x) xs
```

Translating this into a monadic version is relatively simple:

```haskell
sortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
sortM p [] = pure []
sortM p (x:xs) = do
  (gt,le) <- partitionM (p x) xs
  ls <- sortM p le
  gs <- sortM p gt
  pure (ls ++ [x] ++ gs)
  
partitionM :: Applicative m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM p = foldr f (pure ([],[]))
  where
    f e = liftA2 st (p e)
      where
        st True  (tr,fl) = (e:tr,fl)
        st False (tr,fl) = (tr,e:fl)
```

The reason it won't translate into a purely applicative version is that the data we're sending in the recursive case is *generated* by a call to the monadic function. There's an essential [`join`{.haskell}](https://hackage.haskell.org/package/base-4.10.1.0/docs/Control-Monad.html#v:join) happening.

## Decision Trees

I was unconvinced by the logic above. Surely a sorting algorithm will always just produce a decision tree, which could be walked into using only applicatives with `liftA3 ifThenElse`{.haskell} at every branch? In other words:

```haskell
data Tree f a
  = Pure a 
  | Choice (f Bool) (Tree f a) (Tree f a)
```

We'll say the left branch is "true" and the right "false".

*This* type has a monad instance, as it happens:

```haskell
instance Functor (Tree f) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Choice c ts fs) = Choice c (fmap f ts) (fmap f fs)
  
instance Applicative (Tree f) where
  pure = Pure
  Pure f <*> xs = fmap f xs
  Choice c ts fs <*> xs = Choice c (ts <*> xs) (fs <*> xs)
  
instance Monad (Tree f) where
  Pure x >>= f = f x
  Choice c ts fs >>= f = Choice c (ts >>= f) (fs >>= f)
```

We can run the computation with only an applicative constraint on `f`{.haskell}:

```haskell
runTree :: Applicative f => Tree f a -> f a
runTree (Pure x) = pure x
runTree (Choice c ts fs) = liftA3 ifThenElse c (runTree ts) (runTree fs)
  where
    ifThenElse b t f = if b then t else f
```

And it *looks* like we can get our applicative sort:

```haskell
sortA :: Applicative m => (a -> a -> m Bool) -> [a] -> m [a]
sortA p = runTree . sortM (\x y -> Choice (p x y) (Pure True) (Pure False))
```

Except it's not quite right. Trying to get permutations:

```haskell
>>> sortA (\_ _ -> [False,True]) [1,2,3]
[ [1,2,3],[1,3,2],[3,1,2],[3,1,2],[1,2,3],[1,3,2],[3,1,2],[3,1,2],[1,2,3]
, [1,3,2],[3,1,2],[3,1,2],[1,2,3],[1,3,2],[3,1,2],[3,1,2],[2,1,3],[2,1,3]
, [2,1,3],[2,1,3],[2,1,3],[2,1,3],[2,1,3],[2,1,3],[2,3,1],[2,3,1],[2,3,1]
, [2,3,1],[3,2,1],[3,2,1],[3,2,1],[3,2,1]]
```

The issue lies with `liftA3`{.haskell}: because we can't change the shape of computations based on the results from previous, we have to run *both* the true and false branch, multiplying the outcomes. Instead of the $n!$ outcomes from the monadic version, we get $2^{n!-1}$ outcomes!

## Inspection

One of the ways to conceptualize the difference between applicatives and monads is that applicatives are "inspectable", whereas monads aren't. If you look at an applicative computation, it's constructed using things like:

```haskell
(<*>) :: f (a -> b) -> f a -> f b
```

You could imagine deconstructing the built-up tree after the fact, to examine its structure. Monads, on the other hand, have bind:

```haskell
(>>=) :: m a -> (a -> m b) -> m b
```

The issue is the `a -> m b`{.haskell}: to look at the `m b`{.haskell}, you'd have to run the function, but we can't run it without knowing the `a`{.haskell}, and we can't know that with running the `m a`{.haskell}!

However, we *could* run the function if it was something like this:

```haskell
m () -> (() -> m b) -> m b
```

We'd just apply it to `()`{.haskell}. In fact, there are other cases where we could apply it: what about `Bool`{.haskell}? We could apply the function to both `True`{.haskell} and `False`{.haskell} and look at the right-hand results. In fact, that's *kind of* what we did above. Any type, in fact, that is finite would allow us to apply the function to its members.

## Representable

A way to generalise this notion of "finite" is with the [`Representable`{.haskell}](https://hackage.haskell.org/package/adjunctions-4.4/docs/Data-Functor-Rep.html#t:Representable) class. From the package:

> Representable endofunctors over the category of Haskell types are isomorphic to the reader monad and so inherit a very large number of properties for free.

Isomorphic to the reader monad means that we can take something like:

```haskell
a -> b
```

And transform it into

```haskell
f b
```

Which is *exactly* what we're looking for. Here's the plan: take the lambda (`a -> m b`{.haskell}), transform it into its functor, sequenceA to get the applicative out, and finally `liftA2 index`{.haskell}  to combine the results eventually. That will let us build a (kind of) bind for applicatives.

```haskell
class (Rep f ~ UniqueRep f, Representable f) =>
      UniquelyRepresentable f
  where
    type UniqueRep f = x | x -> f

repBind ::
     (Applicative m, UniquelyRepresentable f, Traversable f, a ~ UniqueRep f)
  => m a
  -> (a -> m b)
  -> m b
repBind xs (f :: UniqueRep f -> m b) =
  liftA2 (flip index) xs (sequenceA (tabulate f :: f (m b)))
```

This uses new `TypeFamilyDependencies` extension. It can be done without, but a proxy needs to be passed to the function because the `f`{.haskell} is ambiguous.

Here's an example representation for `Bool`{.haskell}:

```haskell
data Pair a = Pair a a
  deriving (Functor, Foldable,Traversable)

instance Distributive Pair where
  distribute = distributeRep

instance Representable Pair where
  type Rep Pair = Bool
  tabulate f = Pair (f False) (f True)
  index (Pair f t) b = if b then t else f
  
instance UniquelyRepresentable Pair where
  type UniqueRep Pair = Bool
```

Using it, we can generalise the tree type. However, we can use the free monad instead of rolling our own all the time, to cut down on boilerplate:

```haskell
data Choice f a where
  Choice :: (Traversable t, Representable t) 
         => f (Rep t) -> (UniqueRep t -> a) -> Choice f a

instance Functor (Choice f) where
  fmap f (Choice c xs) = Choice c (f . xs)

retractChoice :: Functor f => Choice f a -> f a
retractChoice (Choice x xs) = fmap xs x

runChoice :: Monad m => Choice m (m a) -> m a
runChoice (Choice x xs) = x >>= xs

runChoiceA :: Applicative f => Choice f (f a) -> f a
runChoiceA (Choice c (xs :: UniqueRep t -> f a)) =
  liftA2 (flip index) c (sequenceA (tabulate xs :: t (f a)))

runChoiceMemo :: Monad m => Choice m (m a) -> m a
runChoiceMemo (Choice c (xs :: UniqueRep t -> f a)) = index ys =<< c
  where
    ys :: t (f a)
    ys = tabulate xs

liftFun ::
     (UniquelyRepresentable f, Traversable f)
  => (a -> m (UniqueRep f))
  -> a
  -> Choice m (UniqueRep f)
liftFun (f :: a -> m (UniqueRep f)) x = Choice (f x) id

sortA :: Applicative m => (a -> a -> m Bool) -> [a] -> m [a]
sortA p = 
  iterA runChoiceA . (sortM . curry . fmap liftF . liftFun . uncurry) p
```

In fact, `Choice`{.haskell} itself has a monad instance, I think.

```haskell
instance Applicative f => Applicative (Choice f) where
  pure x = Choice (pure ()) (\() -> x)
  Choice fs f <*> Choice xs x =
    choiceP (Proxy :: Proxy (t :.: s)) (liftA2 (,) fs xs) (\(a, b) -> f a (x b))

instance Applicative f => Monad (Choice f) where
  Choice xs (x :: UniqueRep t -> a) >>= f =
    case traverse f (tabulate x :: t a) of
      Choice ys y ->
        choiceP
          (Proxy :: Proxy (t :.: s))
          (liftA2 (,) xs ys)
          (\(a, b) -> index (y b) a)
```

Although it's slower than lifting to free.

## Uses

So what does this idea correspond to? Well, `Choice`{.haskell} can be wrapped around any applicative, so it actually corresponds to something different for each.

### Parallelism

For a monad representing parallelism, applicative operations usually can be run in parallel, while monadic (those constructed with bind) cannot. [Haxl](https://github.com/facebook/Haxl) makes use of this fact, and goes to great lengths to push as much into applicative operations as possible. However, wrapped in `Choice`{.haskell}, we can perform speculative evaluation: *both* branches of an if-statement can be evaluated while the condition is.
