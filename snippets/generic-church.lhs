---
title: Church-Encode a Datatype, Generically
---

Church-encoding of datatypes is a common pattern you'll see in Haskell. It's possible to do it generically, by using a sum-of-products encoding.

Some preamble:

\begin{code}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables  #-}

module ChurchGen where

import GHC.Generics
import Data.Proxy
import Prelude hiding (take)
import Data.Void
\end{code}

The Church-encoding of something like `Bool`{.haskell} looks like this:

\begin{code}
-- | >>> bool False 1 0
-- 1
bool False f t = f
bool True  f t = t
\end{code}

Kind of like a flipped if statement. To replicate it in generics takes some work:

\begin{code}
class Summable c where
  type Sum c a r :: *
  take :: c p -> (a -> r) -> Sum c a r
  ignore :: Proxy c -> Proxy a -> r -> Sum c a r

class Prodable c where
  type Prod c r :: *
  strip :: c p -> Prod c r -> r

class ChurchGen c where
  type FoldGen c a :: *
  foldGen:: c a -> FoldGen c a

instance Summable c => Summable (M1 i t c) where
  type Sum (M1 i t c) a r = Sum c a r
  take (M1 x) = take x
  ignore (_ :: Proxy (M1 i t c)) = ignore (Proxy :: Proxy c)

instance Prodable c => Prodable (M1 i t c) where
  type Prod (M1 i t c) r = Prod c r
  strip (M1 x) = strip x

instance ChurchGen c => ChurchGen (M1 i t c) where
  type FoldGen (M1 i t c) a = FoldGen c a
  foldGen (M1 x) = foldGen x

instance Summable (K1 i c) where
  type Sum (K1 i c) a r = (c -> a) -> r
  take (K1 x) k f = k (f x)
  ignore _ _ r _ = r

instance Summable U1 where
  type Sum U1 a r = a -> r
  take U1 k f = k f
  ignore _ _ r _ = r

instance Prodable U1 where
  type Prod U1 r = r
  strip U1 x = x

instance ChurchGen U1 where
  type FoldGen U1 a = a -> a
  foldGen U1 x = x

instance Summable V1 where
  type Sum V1 a r = r
  take x = case x of
  ignore _ _ = id

instance Prodable V1 where
  type Prod V1 r = Void -> r
  strip x = case x of

instance Prodable (K1 i c) where
  type Prod (K1 i c) r = c -> r
  strip (K1 x) f = f x

instance ChurchGen (K1 i c) where
  type FoldGen (K1 i c) a = (c -> a) -> a
  foldGen(K1 x) f = f x

instance (Summable li, Summable ri) => Summable (li :+: ri) where
  type Sum (li :+: ri) a r = Sum li a (Sum ri a r)
  take (L1 x) (k :: a -> r) = take x (ignore (Proxy :: Proxy ri) (Proxy :: Proxy a) . k)
  take (R1 x) (k :: a -> r) = ignore (Proxy :: Proxy li) (Proxy :: Proxy a) (take x k)
  ignore p a x = ignore (Proxy :: Proxy li) a (ignore (Proxy :: Proxy ri) a x)

instance (Summable li, Summable ri) => ChurchGen (li :+: ri) where
  type FoldGen (li :+: ri) a = Sum li a (Sum ri a a)
  foldGen(x :: (li :+: ri) a) = take x (id :: a -> a)

instance (Prodable li, Prodable ri) => Prodable (li :*: ri) where
  type Prod (li :*: ri) a = Prod li (Prod ri a)
  strip (li :*: ri) f = strip ri (strip li f)

instance (Prodable li, Prodable ri) => ChurchGen (li :*: ri) where
  type FoldGen (li :*: ri) a = Prod li (Prod ri a) -> a
  foldGen(li :*: ri) f = strip ri (strip li f)

instance (Prodable li, Prodable ri) => Summable (li :*: ri) where
  type Sum (li :*: ri) a r = Prod li (Prod ri a) -> r
  take x k = k . strip x
  ignore _ _ r _ = r

class Church c where
  type Fold c a :: *
  type Fold c a = FoldGen (Rep c) a
  fold :: Proxy a -> c -> Fold c a
  default fold :: (Generic c, ChurchGen (Rep c), FoldGen (Rep c) a ~ Fold c a) => proxy a -> c -> Fold c a
  fold = defaultFold

defaultFold :: (Generic c, ChurchGen (Rep c)) => proxy a -> c -> FoldGen (Rep c) a
defaultFold (p :: proxy a) (x :: c) = foldGen (from x :: Rep c a)
\end{code}

After all of that, we can write the church-encoded bool function like so:

\begin{code}
instance Church Bool

-- | >>> fold (Proxy :: Proxy Int) False 0 1
-- 0
\end{code}
