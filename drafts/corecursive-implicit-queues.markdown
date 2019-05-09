---
title: Implicit Corecursive Queues
series: Breadth-First Traversals
tags: Haskell
---

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

The trouble is, if you try and do that with the above definition, you get
something like the following:

```haskell
bfenum :: Tree a -> [a]
bfenum t = f t b b
  where
    f (Node x xs) fw bw = x : fw (bw . flip (foldr f) xs)
    b x = x b
```

Which comes with type errors:

```
Cannot construct the infinite type: b ~ (b -> c) -> [a]
```

To fix this, we need to wrap the infinite part in a newtype:

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

The problem is that it can't detect an end, so it will never finish the list.
(although it does do everything up until that point correctly)

To change it, we need a slight change to the queue type:

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
