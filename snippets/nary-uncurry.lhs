---
title: liftAN
---

There's a family of functions in [Control.Applicative](https://hackage.haskell.org/package/base-4.11.0.0/docs/Control-Applicative.html) which follow the pattern `liftA2`{.haskell}, `liftA3`{.haskell}, etc. Using some tricks from Richard Eisenberg's thesis we can write them all at once.

\begin{code}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}

module Apply where

data Nat = Z | S Nat

type family AppFunc f (n :: Nat) arrows where
  AppFunc f 'Z a = f a
  AppFunc f ('S n) (a -> b) = f a -> AppFunc f n b

type family CountArgs f where
  CountArgs (a -> b) = 'S (CountArgs b)
  CountArgs result = 'Z

class (CountArgs a ~ n) => Applyable a n where
  apply :: Applicative f => f a -> AppFunc f (CountArgs a) a

instance (CountArgs a ~ 'Z) => Applyable a 'Z where
  apply = id
  {-# INLINE apply #-}

instance Applyable b n => Applyable (a -> b) ('S n) where
  apply f x = apply (f <*> x)
  {-# INLINE apply #-}

-- | >>> lift (\x y z -> x ++ y ++ z) (Just "a") (Just "b") (Just "c")
-- Just "abc"
lift :: (Applyable a n, Applicative f) => (b -> a) -> (f b -> AppFunc f n a)
lift f x = apply (fmap f x)
{-# INLINE lift #-}
\end{code}


[Eisenberg, Richard A. “Dependent Types in Haskell: Theory and Practice.” University of Pennsylvania, 2016.](https://github.com/goldfirere/thesis/raw/master/built/thesis.pdf)
