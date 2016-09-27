---
title: Folding Two Things at Once
tags: Haskell
description: Folding Two Things at Once
---

There's a whole family of Haskell brainteasers surrounding one function: `foldr`{.haskell}. The general idea is to convert some function on lists which uses recursion into one that uses `foldr`{.haskell}. `map`{.haskell}, for instance:

```haskell
map :: (a -> b) -> [a] -> [b]
map f = foldr (\e a -> f e : a) []
```

Some can get a little trickier. `dropWhile`{.haskell}, for instance. (See [here](https://wiki.haskell.org/wikiupload/1/14/TMR-Issue6.pdf) and [here](http://www.cs.nott.ac.uk/~pszgmh/fold.pdf) for interesting articles on that one in particular.)

```haskell
dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile p = fst . foldr f ([],[]) where
  f e ~(xs,ys) = (if p e then xs else zs, zs) where zs = e : ys
```

## Zip

One function which was a little harder to convert than it first seemed was `zip`{.haskell}.

Here's the first (non) solution:

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip = foldr f (const []) where
  f x xs (y:ys) = (x,y) : xs ys
  f _ _  [] = []
```

The problem with the above isn't that it doesn't work: it does. The problem is that it's not *really* using `foldr`{.haskell}. It's only using it on the first list: there's still a manual uncons being performed on the second. Ideally, I would want the function to look something like this:

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip xs ys = foldr f (\_ _ -> []) xs (foldr g (const []) ys)
```

The best solution I found online only dealt with `Fold`{.haskell}s, not `Foldable`{.haskell}s. You can read it [here](http://okmij.org/ftp/Haskell/zip-folds.lhs).

## Recursive Types

Reworking the solution online for `Foldable`{.haskell}s, the initial intuition is to have the `foldr`{.haskell} on the `ys`{.haskell} produce a function which takes an element of the `xs`{.haskell}, and returns a function which takes an element of the `xs`{.haskell}, and so on, finally returning the created list. The *problem* with that approach is the types involved:

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip xs = foldr f (const []) xs . foldr g (\_ _ -> []) where
  g e2 r2 e1 r1 = (e1,e2) : (r1 r2)
  f e r x = x e r
```

You get the error:

> `Occurs check: cannot construct the infinite type: t0 ~ a -> (t0 -> [(a, b)]) -> [(a, b)]`{.haskell}.

Haskell's typechecker doesn't allow for infinitely recursive types. 

You'll be familiar with this problem if you've ever tried to encode the Y-combinator, or if you've fiddled around with the recursion-schemes package. You might also be familiar with the solution: a `newtype`{.haskell}, encapsulating the recursion. In this case, the `newtype`{.haskell} looks very similar to the signature for `foldr`{.haskell}:

```haskell
newtype RecFold a b = 
  RecFold { runRecFold :: a -> (RecFold a b -> b) -> b }
```

Now you can insert and remove the `RecFold`{.haskell} wrapper, helping the typechecker to understand the recursive types as it goes:

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip xs =
  foldr f (const []) xs . RecFold . foldr g (\_ _ -> []) where
    g e2 r2 e1 r1 = (e1,e2) : (r1 (RecFold r2))
    f e r x = runRecFold x e r
```

As an aside, the performance characteristics of the `newtype`{.haskell} wrapper are totally opaque to me. There may be significant improvements by using `coerce`{.haskell} from [Data.Coerce](https://hackage.haskell.org/package/base-4.8.2.0/docs/Data-Coerce.html), but I haven't looked into it.

## Generalised Zips

The immediate temptation from the function above is to generalise it. First to `zipWith`{.haskell}, obviously:

```haskell
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith c xs =
  foldr f (const []) xs . RecFold . foldr g (\_ _ -> []) where
    g e2 r2 e1 r1 = c e1 e2 : (r1 (RecFold r2))
    f e r x = runRecFold x e r
```

What's maybe a little more interesting, though, would be a `foldr`{.haskell} on two lists. Something which folds through both at once, using a supplied combining function:

```haskell
foldr2 :: (Foldable f, Foldable g)
       => (a -> b -> c -> c)
       -> c -> f a -> g b -> c
foldr2 c i xs =
  foldr f (const i) xs . RecFold . foldr g (\_ _ -> i) where
    g e2 r2 e1 r1 = c e1 e2 (r1 (RecFold r2))
    f e r x = runRecFold x e r
```

Of course, once you can do two, you can do three:

```haskell
foldr3 :: (Foldable f, Foldable g, Foldable h)
       => (a -> b -> c -> d -> d)
       -> d -> f a -> g b -> h c -> d
foldr3 c i xs ys =
  foldr f (const i) xs . RecFold . foldr2 g (\_ _ -> i) ys where
    g e2 e3 r2 e1 r1 = c e1 e2 e3 (r1 (RecFold r2))
    f e r x = runRecFold x e r
```

And so on.

There's the added benefit that the above functions work on much more than just lists.

## Catamorphisms

Getting a little formal about the above functions, a `fold`{.haskell} can be described as a catamorphism. This is a name for a pattern of breaking down some recursive structure. There's a bunch of them in the [recursion-schemes](https://hackage.haskell.org/package/recursion-schemes-4.1.2/docs/Data-Functor-Foldable.html) package. The question is, then: can you express the above as a kind of catamorphism? Initially, using the same techniques as before, you can:

```haskell
newtype RecF f a = RecF { unRecF :: Base f (RecF f a -> a) -> a }

zipo :: (Functor.Foldable f, Functor.Foldable g)
     => (Base f (RecF g c) -> Base g (RecF g c -> c) -> c)
     -> f -> g -> c
zipo alg xs ys = cata (flip unRecF) ys (cata (RecF . alg) xs)
```

Then, coming full circle, you get a quite nice encoding of `zip`{.haskell}:

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip = zipo alg where
  alg Nil _ = []
  alg _ Nil = []
  alg (Cons x xs) (Cons y ys) = (x, y) : ys xs
```

However, the `RecF`{.haskell} is a little ugly. In fact, it's possible to write the above without any recursive types, using the RankNTypes extension. (It's possible that you could do the same with `foldr2`{.haskell} as well, but I haven't figured it out yet)

You can actually use a `newtype`{.haskell} that's provided by the recursion-schemes library as-is. It's `Mu`{.haskell}. This is required for an encoding of the Y-combinator. It's usually presented in this form:

```haskell
newtype Mu a = Roll { unroll :: Mu a -> a }
```

However, in the recursion-schemes package, its definition looks like this:

```haskell
newtype Mu f = Mu (forall a. (f a -> a) -> a)
```

No recursion! The `zipo`{.haskell} combinator above can be written using `Mu`{.haskell} like so:

```haskell
zipo :: (Functor.Foldable f, Functor.Foldable g)
     => (Base f (Mu (Base g) -> c) -> Base g (Mu (Base g)) -> c)
     -> f -> g -> c
zipo alg xs = cata (\x -> alg x . project) xs . refix
```

And the new version of `zip`{.haskell} has a slightly more natural order of arguments:

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip = zipo alg where
  alg Nil _ = []
  alg _ Nil = []
  alg (Cons x xs) (Cons y ys) = (x,y) : xs ys
```

## Zipping Into

There's one more issue, though, that's slightly tangential. A lot of the time, the attraction of rewriting functions using folds and catamorphisms is that the function becomes more general: it no longer is restricted to lists. For `zip`{.haskell}, however, there's still a pesky list left in the signature:

```haskell
zip :: (Foldable f, Foldable g) => f a -> g b -> [(a,b)]
```

It would be a little nicer to be able to zip through something *preserving* the structure of one of the things being zipped through. For no reason in particular, let's assume we'll preserve the structure of the first argument. The function will have to account for the second argument running out before the first, though. A `Maybe`{.haskell} can account for that:

```haskell
zipInto :: (Foldable f, Foldable g) 
        => (a -> Maybe b -> c) 
        -> f a -> g b -> f c
```

If the second argument runs out, `Nothing`{.haskell} will be passed to the combining function.

It's clear that this isn't a *fold* over the first argument, it's a *traversal*. A first go at the function uses the state monad, but restricts the second argument to a list:

```haskell
zipInto :: Traversable f => (a -> Maybe b -> c) -> f a -> [b] -> f c
zipInto c xs ys = evalState (traverse f xs) ys where
  f x = do
    h <- gets uncons
    case h of 
      Just (y,t) -> do 
        put t
        pure (c x (Just y))
      Nothing -> pure (c x Nothing)
```

That code can be cleaned up a little:

```haskell
zipInto :: Traversable f => (a -> Maybe b -> c) -> f a -> [b] -> f c 
zipInto c = evalState . traverse (state . f . c) where
  f x [] = (x Nothing, [])
  f x (y:ys) = (x (Just y), ys)
```

But really, the uncons needs to go. Another `newtype`{.haskell} wrapper is needed, and here's the end result:

```haskell
newtype RecAccu a b =
  RecAccu { runRecAccu :: a -> (RecAccu a b, b) }
  
zipInto :: (Traversable t, Foldable f)
        => (a -> Maybe b -> c) -> t a -> f b -> t c
zipInto f xs =
  snd . flip (mapAccumL runRecAccu) xs . RecAccu . foldr h i where
    i e = (RecAccu i, f e Nothing)
    h e2 a e1 = (RecAccu a, f e1 (Just e2))
```
