---
title: Strict Applicative Transformer
---

Adapted from [this post](https://www.reddit.com/r/haskell/comments/86021n/strictifying_traversals/) on reddit. It's possible to take a lazy traversal and make it strict.

\begin{code}
{-# LANGUAGE BangPatterns #-}

module Seq (fmap',traverse') where

import Data.Coerce
import Control.Applicative (liftA2)

newtype Seq a = Seq { unSeq :: a }

instance Functor Seq where
  fmap f x = let !vx = unSeq x in Seq (f vx)
  {-# INLINE fmap #-}
  x <$ xs = let !_ = unSeq xs in Seq x
  {-# INLINE (<$) #-}

instance Applicative Seq where
  pure = Seq
  {-# INLINE pure #-}
  fs <*> xs = let !vx = unSeq xs in Seq (unSeq fs vx)
  {-# INLINE (<*>) #-}
  xs *> ys = let !_ = unSeq xs in ys
  {-# INLINE (*>) #-}
  xs <* ys = let !_ = unSeq ys in xs
  {-# INLINE (<*) #-}

fmap' :: Traversable f => (a -> b) -> f a -> f b
fmap' = (coerce :: ((a -> Seq b) -> f a -> Seq (f b)) -> (a -> b) -> f a -> f b) traverse
{-# INLINE fmap' #-}

newtype SeqT f a = SeqT { unSeqT :: f a }

instance Functor f => Functor (SeqT f) where
  fmap f = SeqT #. fmap (\ !vx -> f vx) .# unSeqT
  {-# INLINE fmap #-}

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce
{-# INLINE (#.) #-}

(.#) :: Coercible a b => (b -> c) -> (a -> b) -> a -> c
(.#) f _ = coerce f
{-# INLINE (.#) #-}

instance Applicative f => Applicative (SeqT f) where
  pure = SeqT #. pure
  {-# INLINE pure #-}
  (<*>) = (coerce :: (f (a -> b) -> f a -> f b) -> (SeqT f (a -> b) -> SeqT f a -> SeqT f b)) (liftA2 (\fs !vx -> fs vx))
  {-# INLINE (<*>) #-}
  liftA2 f = (coerce :: (f a -> f b -> f c) -> (SeqT f a -> SeqT f b -> SeqT f c)) (liftA2 (\ !x !y -> f x y))
  {-# INLINE liftA2 #-}

traverse' :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
traverse' = (coerce :: ((a -> SeqT f b) -> t a -> SeqT f (t b)) -> (a -> f b) -> t a -> f (t b)) traverse
{-# INLINE traverse' #-}
\end{code}

You need traversable in order to get the strictness: there's a similar way to get a stricter fmap [with monad instead](http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Monad.html#v:-60--36--33--62-):

\begin{code}
(<$!>) :: Monad m => (a -> b) -> m a -> m b
{-# INLINE (<$!>) #-}
f <$!> m = do
  x <- m
  let z = f x
  z `seq` return z
\end{code}
