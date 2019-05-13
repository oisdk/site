---
title: Implicit Corecursive Queues
series: Breadth-First Traversals
tags: Haskell
bibliography: Rose Tree Traversals.bib
---

# Fusion

I was looking again at one of my implementations of breadth-first traversals:

```haskell
bfe :: Tree a -> [a]
bfe r = f r b []
  where
    f (Node x xs) fw bw = x : fw (xs : bw)
  
    b [] = []
    b qs = foldl (foldr f) b qs []
```

And I was wondering if I could *fuse* away the intermediate list.
On the following line:

```haskell
f (Node x xs) fw bw = x : fw (xs : bw)
```

The `xs : bw` is a little annoying, because we *know* it's going to be consumed
eventually by a fold.
When that happens, it's often a good idea to remove the list, and just inline
the fold.
In other words, if you see the following:

```haskell
foldr f b (x : y : [])
```

You should replace it with this:

```haskell
f x (f y b)
```

If you try and do that with the above definition, you get something like the
following:

```haskell
bfenum :: Tree a -> [a]
bfenum t = f t b b
  where
    f (Node x xs) fw bw = x : fw (bw . flip (foldr f) xs)
    b x = x b
```

# Infinite Types

The trouble is that the above comes with type errors:

```
Cannot construct the infinite type: b ~ (b -> c) -> [a]
```

This error shows up occasionally when you try and do heavy church-encoding in
Haskell.
You get a similar error when trying to encode the Y combinator:

```haskell
y = \f -> (\x -> f (x x)) (\x -> f (x x))
```
```
• Occurs check: cannot construct the infinite type: t0 ~ t0 -> t
```

The solution for the y combinator is to use a newtype, where we can catch the
recursion at a certain point to help the typechecker.

```haskell
newtype Mu a = Mu (Mu a -> a)
y f = (\h -> h $ Mu h) (\x -> f . (\(Mu g) -> g) x $ x)
```

The trick for our queue is similar:

```haskell
newtype Q a = Q { q :: (Q a -> [a]) -> [a] }

bfenum :: Tree a -> [a]
bfenum t = q (f t b) e
  where
    f (Node x xs) fw = Q (\bw -> x : q fw (bw . flip (foldr f) xs))
    b = fix (Q . flip id)
    e = fix (flip q)
```

This is actually equivalent to the continuation monad:

```haskell
newtype Fix f = Fix { unFix :: f (Fix f) }

type Q a = Fix (ContT a [])

q = runContT . unFix

bfenum :: Tree a -> [a]
bfenum t = q (f t b) e
  where
    f (Node x xs) fw = Fix (mapContT (x:) (flip (foldr f) xs <$> unFix fw))
    b = fix (Fix . pure)
    e = fix (flip q)
```

# Terminating

There's a problem though: this algorithm never checks for an end.
That's ok if there isn't one, mind you.
For instance, with the following "unfold" function:

```haskell
infixr 9 #.
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce
{-# INLINE (#.) #-}

bfUnfold :: (a -> (b,[a])) -> a -> [b]
bfUnfold f t = g t (fix (Q #. flip id)) (fix (flip q))
  where
    g b fw bw = x : q fw (bw . flip (foldr ((Q .) #. g)) xs)
      where
        (x,xs) = f b
```

We can write a decent enumeration of the rationals.

```haskell
-- Stern-Brocot
rats1 :: [Rational]
rats1 = bfUnfold step ((0,1),(1,0))
  where
    step (lb,rb) = (n % d,[(lb , m),(m , rb)])
      where
        m@(n,d) = adj lb rb
    adj (w,x) (y,z) = (w+y,x+z)
    
-- Calkin-Wilf
rats2 :: [Rational]
rats2 = bfUnfold step (1,1)
  where
    step (m,n) = (m % n,[(m,m+n),(n+m,n)])
```

However, if we *do* want to stop at some point, we need a slight change to the
queue type.

```haskell
newtype Q a = Q { q :: Maybe (Q a -> [a]) -> [a] }

bfenum :: Tree a -> [a]
bfenum t = q (f t b) e
  where 
    f (Node x xs) fw = Q (\bw -> x : q fw (Just (m bw . flip (foldr f) xs)))
    b = fix (Q . maybe [] . flip ($))
    e = Nothing
    m = fromMaybe (flip q e)
```

# Monadic

We can actually add in a monad to the above unfold without much difficulty. 

```haskell
newtype Q m a = Q { q :: Maybe (Q m a -> m [a]) -> m [a] }

bfUnfold :: Monad m => (a -> m (b,[a])) -> a -> m [b]
bfUnfold f t = g t b e
  where
    g s fw bw = f s >>= 
       \ ~(x,xs) -> (x :) <$>  q fw (Just (m bw . flip (foldr ((Q .) #. g)) xs))
        
    b = fix (Q #. maybe (pure []) . flip ($))
    e = Nothing
    m = fromMaybe (flip q e)
```

And it passes the torture tests for a linear-time breadth-first unfold from
@feuer_is_2015.
It breaks when you try and use it to build a tree, though.

# Phases

Finally, we can try and make the above code a little more modular, by actually
packaging up the queue type as a queue.

```haskell
newtype Q a = Q { q :: Maybe (Q a -> [a]) -> [a] }
newtype Queue a = Queue { runQueue :: Q a -> Q a }

now :: a -> Queue a
now x = Queue (\fw -> Q (\bw -> x : q fw bw))
    
delay :: Queue a -> Queue a
delay xs = Queue (\fw -> Q (\bw -> q fw (Just (m bw . runQueue xs))))
  where
    m = fromMaybe (flip q Nothing)
    
instance Monoid (Queue a) where
    mempty = Queue id
    mappend (Queue xs) (Queue ys) = Queue (xs . ys)
    
run :: Queue a -> [a]
run (Queue xs) = q (xs b) Nothing
  where
    b = fix (Q . maybe [] . flip ($))

bfenum :: Tree a -> [a]
bfenum t = run (f t)
  where 
    f (Node x xs) = now x <> delay (foldMap f xs)
```

At this point, our type is starting to look a lot like the
[`Phases`](https://hackage.haskell.org/package/tree-traversals-0.1.0.0/docs/Control-Applicative-Phases.html#t:Phases)
type from Noah Easterly's tree-traversals package.
This is exciting: the `Phases` type has the ideal interface for level-wise
traversals.
Unfortunately, it has the wrong time complexity for `<*>` and so on: my
suspicion is that the queue type above here is to `Phases` as the continuation
monad is to the free monad.
In other words, we'll get efficient construction at the expense of no
inspection.
Unfortunately, I can't figure out how to turn the above type into an
applicative.
Maybe in a future post!

Finally, a lot of this is working towards finally understanding
@smith_lloyd_2009 and @allison_circular_2006.
