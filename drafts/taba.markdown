---
title: Typing TABA
tags: Haskell
---

Just a short one again today!

There's an [excellent talk](https://www.youtube.com/watch?v=u_OsUlwkmBQ) by
Kenneth Foner at Compose from 2016 which goes through a paper by Danvy &
Goldberg called "There and Back Again" (or TABA).
You should watch the talk and read the paper if you're in any way excited by the
weird and wonderful algorithms we use in functional languages to do simple
things like reversing a list.

The function focused on in the paper is one which does the following:

```haskell
zipRev :: [a] -> [b] -> [(a,b)]
zipRev xs ys = zip xs (reverse ys)
```

But does it in one pass, *without* reversing the second list.
It uses a not-insignificant bit of cleverness to do it, but we can actually do
it in Haskell quite straightforwardly by applying best practice, which says we
should use folds wherever we can.
The result is the following:

```haskell
zipRev :: [a] -> [b] -> [(a,b)]
zipRev xs ys = foldl f b ys xs
  where
    b _ = []
    f k y (x:xs) = (x,y) : k xs
```

The talk goes through the same stuff, but takes a turn then to proving the
function total: our version above won't work correctly if the lists don't have
the same length, so it would be nice to provide that guarantee in the types
somehow.
Directly translating the version from the TABA paper into one which uses
length-indexed vectors will require some nasty, expensive proofs, though, which
end up making the whole function quadratic.

As ever, we can actually solve the problem again by using a fold!
To demonstrate this rather short solution, we'll first need the regular toolbox
of types:

```haskell
data Nat = Z | S Nat

data Vec (a :: Type) (n :: Nat) where
  Nil :: Vec a Z
  (:-) :: a -> Vec a n -> Vec a (S n)
```

And now we will write a length-indexed left fold on this vector.
The combined power of coerce and newtypes gives us type safety without a
performance hit, resulting in the following linear-time function:

```haskell
newtype (:.:) (f :: b -> Type) (g :: a -> b) (x :: a) = Comp { unComp :: f (g x) }

foldlVec :: forall a b n. (forall m. a -> b m -> b (S m)) -> b Z -> Vec a n -> b n
foldlVec f b Nil = b
foldlVec f b (x :- xs) = unComp (foldlVec (c f) (Comp (f x b)) xs)
  where
    c :: (a -> b (S m) -> b (S (S m))) -> (a -> (b :.: S) m -> (b :.: S) (S m))
    c = coerce
    {-# INLINE c #-}
```

Now, to write the reversing zip, we need another newtype to put the parameter in
the right place, but it is straightforward other than that.

```haskell
newtype VecCont a b n = VecCont { runVecCont :: Vec a n -> Vec (a,b) n }

revZip :: Vec a n -> Vec b n -> Vec (a,b) n
revZip = flip $ runVecCont . 
  foldlVec
      (\y k -> VecCont (\(x :- xs) -> (x,y) :- runVecCont k xs))
      (VecCont (const Nil))
```
