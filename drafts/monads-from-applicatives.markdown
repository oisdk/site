---
title: Getting Monads From Applicatives
tags: Haskell, applicative
bibliography: Monads vs Applicatives.bib
---

In my post on [monadic list functions](2018-02-11-monadic-list.functions.html), we went through a couple functions from Data.List that have the "m" suffix—[`filterM`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Control-Monad.html#v:filterM) and so on. We saw that when you specialized the monad to the list monad, you often got more complex but related functions for free. Finally, we saw that while most of these functions actually only required an Applicative constraint, some—the sorting algorithms in particular—did indeed need Monad.

Here's a refresher on the monadic version of ([not](http://augustss.blogspot.ie/2007/08/quicksort-in-haskell-quicksort-is.html)) quicksort:

```haskell
partitionM :: Applicative m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM p = foldr f (pure ([],[])) where
  f x = liftA2 ifStmt (p x) where
    ifStmt flg (tr,fl)
      | flg = (x:tr,fl)
      | otherwise = (tr,x:fl)
      
quickSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
quickSortM p [] = pure []
quickSortM p (x:xs) = do
  (gt,le) <- partitionM (p x) xs
  ls <- quickSortM p le
  gs <- quickSortM p gt
  pure (ls ++ [x] ++ gs)
```

The reason it won't translate into a purely applicative version is that the data we're sending in the recursive case is *generated* by a call to the monadic function. There's an essential [`join`{.haskell}](https://hackage.haskell.org/package/base-4.10.1.0/docs/Control-Monad.html#v:join) happening.

## Decision Trees

Towards the end of the last post, we used decision trees to generate nice diagrams for each algorithm. Before printing out the result, this was the basic function we used:

```haskell
data DecTree t a
  = Pure a
  | Choice t (DecTree t a) (DecTree t a)
  deriving Functor

instance Applicative (DecTree t) where
  pure = Pure
  Pure f <*> xs = fmap f xs
  Choice c ls rs <*> xs = Choice c (ls <*> xs) (rs <*> xs)
  
instance Monad (DecTree t) where
  Pure x >>= f = f x
  Choice c ls rs >>= f = Choice c (ls >>= f) (rs >>= f)

traceCompare :: a -> a -> DecTree (a,a) Bool
traceCompare x y = Choice (x,y) (Pure True) (Pure False)
```

Here's where we can start seeing a potential route to using an applicative: the `DecTree`{.haskell} type is a free monad, so we could interpret it in any way we choose. And there's a very obvious applicative interpretation of the above:

```haskell
quickSortDecTree :: [a] -> DecTree (a,a) [a]
quickSortDecTree = quickSortM traceCompare

runTree :: Applicative f 
        => (a -> a -> f Bool) -> DecTree (a,a) b -> f b
runTree _ (Pure x) = pure x
runTree p (Choice (x,y) tr fl) =
    liftA3 ifThenElse (p x y) (runTree p tr) (runTree p fl)
    
quickSortA :: Applicative f => (a -> a -> f Bool) -> [a] -> f [a]
quickSortA p = runTree p . quickSortDecTree
```

We can now try it with the classic "applicative-not-monad":

```haskell
bothSort = getZipList . quickSortA (\x y -> ZipList [x <= y, y <= x])

>>> bothSort [1,4,2,3,5]
[[1,2,3,4,5],[5,4,3,2,1]]
```

As you can see, this sorts the list both in order and reversed. It's a decent demonstration of the difference between applicative ziplists and applicative lists: the former runs many parallel computations, the latter many *branching* computations.

So surely the new version is better? The types look similar, but with a lesser constraint. Should we now just use the applicative version everywhere? Well, no: check out the output when we try it again with normal lists.

```haskell
>>> quickSortA (\_ _ -> [False,True]) [1,2,3]
[ [3,2,1],[2,3,1],[2,1,3],[2,1,3],[3,2,1],[2,3,1],[2,1,3],[2,1,3],[3,2,1]
, [2,3,1],[2,1,3],[2,1,3],[3,2,1],[2,3,1],[2,1,3],[2,1,3],[3,1,2],[3,1,2]
, [3,1,2],[3,1,2],[3,1,2],[3,1,2],[3,1,2],[3,1,2],[1,3,2],[1,3,2],[1,3,2]
, [1,3,2],[1,2,3],[1,2,3],[1,2,3],[1,2,3]]
```

There's a huge amount of repeated output here. Instead of the $n!$ outcomes from the monadic version, we get $2^{n!-1}$ outcomes!

## No Free Lunch

The problem we're facing here is actually described in the original paper on applicatives [@mcbride_applicative_2008], with the two functions "miffy" and "iffy":

```haskell
miffy :: Monad m => m Bool -> m a -> m a -> m a
miffy mb mt me = do
  b <- mb
  if b then mt else me

iffy :: Applicative f => f Bool -> f a -> f a -> f a
iffy fb ft fe = liftA3 cond fb ft fe where
  cond b t e = if b then t else e
```

In `miffy`{.haskell}, we can choose which effect to execute based on the result of previous computations. However, that's *precisely* what applicatives can't do. So, in `iffy`{.haskell}, we choose the *result* of a computation based on previous computations, but both the true and false branch have to be executed (effects-wise) regardless. That's why we get the combinatorial explosion above: every branch is explored, with no pruning.

## Inspection

Another way to conceptualize the difference in power between applicatives and monads is through the "staticness" of computations built by them. Applicatives have a static, predefined structure once the computation is built up: monads on the other hand, have to deal with `>>=`{.haskell}.

```haskell
(>>=) :: m a -> (a -> m b) -> m b
```

The structure of the first `m b`{.haskell} is totally inaccessible to us: if we wanted to look at it, we'd have to run the `a -> m b`{.haskell}, and we can't do that without an `a`{.haskell}.

We might have an `a`{.haskell} to give it in some cases, though. `()`{.haskell} is one: we just give the function a `()`{.haskell} and we can look at it all we want. `Bool`{.haskell} is another: we give it a `True`{.haskell}, and a `False`{.haskell}, and look at both outcomes. In fact, that's exactly what we did above.

## Representable

So there are some types that will let us run functions on them from all possible inputs. The generalization of this is the [`Representable`{.haskell}](https://hackage.haskell.org/package/adjunctions-4.4/docs/Data-Functor-Rep.html#t:Representable) class. From the package:

> Representable endofunctors over the category of Haskell types are isomorphic to the reader monad and so inherit a very large number of properties for free[^rep-explanation].

[^rep-explanation]: If that explanation is a little dense, here's how you can think about it: by something being "isomorphic" to the reader monad, it means that you can convert it to and from a function. So for booleans:

      `Bool -> b`{.haskell}
      
      Can be changed to something else, and back again. The something else we're going to be changing it to is what will let us look at all possible outputs.

Which is *exactly* what we're looking for.

Here's the plan: take the lambda (`a -> m b`{.haskell}), transform it into its functor, sequenceA to get the applicative out, and finally `liftA2 index`{.haskell}  to combine the results eventually. That will let us build a (kind of) bind for applicatives.

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

Using it, we can generalise the tree type. However, we can use the free monad instead of rolling our own all the time, to cut down on boilerplate[^choice-monad]:

```haskell
data Choice f a where
  Choice :: (Traversable t, UniquelyRepresentable t) 
         => f (Rep t) -> (UniqueRep t -> a) -> Choice f a

instance Functor (Choice f) where
  fmap f (Choice c xs) = Choice c (f . xs)

runChoiceA :: Applicative f => Choice f (f a) -> f a
runChoiceA (Choice c (xs :: UniqueRep t -> f a)) =
  liftA2 (flip index) c (sequenceA (tabulate xs :: t (f a)))

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

[^choice-monad]: In fact, `Choice`{.haskell} itself has a monad instance, I think.

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

## Implications

So we can get a monad from an applicative when we can traverse all of the available inputs. What does that mean when specialized to different applicatives? The one that jumps to mind for me is [speculative execution](https://en.wikipedia.org/wiki/Speculative_execution). If you have an applicative that is used for running computations in parallel ([Haxl](https://github.com/facebook/Haxl)), the `iffy`{.haskell} function above will execute the condition computation, true branch, and false branch at once. The `repBind`{.haskell} is a generalization of this.

The second thing is [belief propagation](https://en.wikipedia.org/wiki/Belief_propagation). 
