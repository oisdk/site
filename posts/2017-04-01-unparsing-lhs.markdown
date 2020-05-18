---
title: Unparsing
tags: Haskell
---

Pretty-printing expressions with minimal parenthesis is a little trickier than it looks. This algorithm is adapted from:

[Ramsey, Norman. ‘Unparsing Expressions With Prefix and Postfix Operators’. Software—Practice & Experience 28, no. 12 (1998): 1327–1356.](https://www.cs.tufts.edu/~nr/pubs/unparse-abstract.html)

```haskell
{-# LANGUAGE DeriveFunctor #-}

module Unparse where

import Data.Semigroup
import Data.Coerce

data Side
    = L
    | R
    deriving Eq

data ShowExpr t e
    = Lit     {repr :: t}
    | Prefix  {repr :: t, op :: Op, child :: e}
    | Postfix {repr :: t, op :: Op, child :: e}
    | Binary  {repr :: t, op :: Op, lchild :: e, rchild :: e}
    deriving Functor

data Op = Op
    { prec :: Int
    , assoc :: Side
    }

showExpr
    :: Semigroup t
    => (e -> ShowExpr t e) -> (t -> t) -> e -> t
showExpr proj prns = go . fmap proj . proj
  where
    go (Lit t) = t
    go (Prefix t o y) = t <> ifPrns R o (getOp y) (go (fmap proj y))
    go (Postfix t o x) = ifPrns L o (getOp x) (go (fmap proj x)) <> t
    go (Binary t o x y) =
        ifPrns L o (getOp x) (go (fmap proj x)) <> t <>
        ifPrns R o (getOp y) (go (fmap proj y))
    ifPrns sid (Op op oa) (Just (Op ip ia))
      | ip < op || ip == op && (ia /= oa || sid /= oa) = prns
    ifPrns _ _ _ = id
    getOp Lit{} = Nothing
    getOp e = Just (op e)

showSExpr :: (e -> ShowExpr ShowS e) -> e -> ShowS
showSExpr proj =
    appEndo .
    showExpr
        (coerce proj)
        (coerce (showParen True))
```

And an example of its use:

```haskell
data Expr = Number Integer
          | Expr :+: Expr
          | Expr :*: Expr
          | Expr :^: Expr

instance Num Expr where
  (+) = (:+:)
  (*) = (:*:)
  fromInteger = Number
  abs = undefined
  signum = undefined
  negate = undefined

-- | >>> default (Expr)
--
-- >>> 1 + 2 + 3
-- 1 + 2 + 3
--
-- >>> 1 * 2 * 3
-- 1 * 2 * 3
--
-- >>> (1 * 2) + 3
-- 1 * 2 + 3
--
-- >>> 1 * (2 + 3)
-- 1 * (2 + 3)
--
-- >>> (1 :^: 2) :^: 3
-- (1 ^ 2) ^ 3
--
-- >>> 1 :^: (2 :^: 3)
-- 1 ^ 2 ^ 3
instance Show Expr where
  showsPrec _ = showSExpr proj where
    proj (Number n) = Lit (shows n)
    proj (x :+: y) = Binary (showString " + ") (Op 3 L) x y
    proj (x :*: y) = Binary (showString " * ") (Op 4 L) x y
    proj (x :^: y) = Binary (showString " ^ ") (Op 5 R) x y
```
