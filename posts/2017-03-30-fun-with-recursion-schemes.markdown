---
title: Fun with Recursion Schemes
tags: Haskell, Recursion Schemes
bibliography: PrettyPrinting.bib
---

## Folding Algebras

I saw [this](https://www.reddit.com/r/haskell/comments/608y0l/would_this_sugar_make_sense/) post on reddit recently, and it got me thinking about recursion schemes. One of the primary motivations behind them is the reduction of boilerplate. The classic example is evaluation of arithmetic expressions:

```{.haskell}
data ExprF a
  = LitF Integer
  | (:+:) a a
  | (:*:) a a
  deriving Functor

type Expr = Fix ExprF

eval :: Expr -> Integer
eval = unfix >>> \case
  LitF n -> n
  x :+: y -> eval x + eval y
  x :*: y -> eval x * eval y
```

The calls to `eval`{.haskell} are the boilerplate: this is where the main recursion scheme, `cata`{.haskell} can help.

```{.haskell}
evalF :: Expr -> Integer
evalF = cata $ \case
  LitF n -> n
  x :+: y -> x + y
  x :*: y -> x * y
```

I still feel like there's boilerplate, though. Ideally I'd like to write this:

```{.haskell}
evalF :: Expr -> Integer
evalF = cata $ ??? $ \case
  Lit -> id
  Add -> (+)
  Mul -> (*)
```

The `???`{.haskell} needs to be filled in. It's a little tricky, though: the type of the algebra changes depending on what expression it's given. GADTs will allow us to attach types to cases:

```{.haskell}
data ExprI a r f where
  Lit :: ExprI a b (Integer -> b)
  Add :: ExprI a b (a -> a -> b)
  Mul :: ExprI a b (a -> a -> b)
```

The first type parameter is the same as the first type parameter to `ExprF`{.haskell}. The second is the output type of the algebra, and the third is the type of the fold required to produce that output type. The third type parameter *depends* on the case matched in the GADT. Using this, we can write a function which converts a fold/pattern match to a standard algebra:

```{.haskell}
foldAlg :: (forall f. ExprI a r f -> f) -> (ExprF a -> r)
foldAlg f (LitF i)  = f Lit i
foldAlg f (x :+: y) = f Add x y
foldAlg f (x :*: y) = f Mul x y
```

And finally, we can write the nice evaluation algebra:

```{.haskell}
evalF :: Expr -> Integer
evalF = cata $ foldAlg $ \case
  Lit -> id
  Add -> (+)
  Mul -> (*)
```

I hacked together some quick template Haskell to generate the matchers over [here](https://github.com/oisdk/pattern-folds). It uses a class `AsPatternFold`{.haskell}:

```{.haskell}
class AsPatternFold x f | x -> f where
  foldMatch :: (forall a. f r a -> a) -> (x -> r)
```

And you generate the extra data type, with an instance, by doing this:

```{.haskell}
makePatternFolds ''ExprF
```

The code it generates can be used like this:

```{.haskell}
evalF :: Expr -> Integer
evalF = cata $ foldMatch $ \case
  LitI -> id
  (:+|) -> (+)
  (:*|) -> (*)
```

It's terribly hacky at the moment, I may clean it up later.

## Record Case

There's another approach to the same idea that is slightly more sensible, using record wildcards. You define a handler for you datatype (an algebra):

```{.haskell}
data ExprAlg a r
  = ExprAlg
  { litF :: Integer -> r
  , (+:) :: a -> a -> r
  , (*:) :: a -> a -> r }
```

Then, to use it, you define how to interact between the handler and the datatype, like before. The benefit is that record wildcard syntax allows you to piggy back on the function definition syntax, like so:

```{.haskell}
data ExprF a
  = LitF Integer
  | (:+:) a a
  | (:*:) a a

makeHandler ''ExprF

exprAlg :: ExprF Integer -> Integer
exprAlg = index ExprFAlg {..} where
  litF = id
  (+:) = (+)
  (*:) = (*)
```

This approach is much more principled: the `index`{.haskell} function, for example, comes from the [adjunctions](https://hackage.haskell.org/package/adjunctions) package, from the [`Representable`{.haskell}](https://hackage.haskell.org/package/adjunctions-4.3/docs/Data-Functor-Rep.html) class. That's because those algebras are actually representable functors, with their representation being the thing they match. They also conform to a whole bunch of things automatically, letting you combine them interesting ways. 


## Printing Expressions

Properly printing expressions, with minimal parentheses, is a surprisingly difficult problem. @ramsey_unparsing_1998 provides a solution of the form:

```{.haskell}
isParens side (Assoc ao po) (Assoc ai pi) =
  pi <= po && (pi /= po || ai /= ao || ao /= side)
```

Using this, we can write an algebra for printing expressions. It should work in the general case, not just on the expression type defined above, so we need to make another unfixed functor to describe the printing of an expression:

```{.haskell}
data Side = L | R deriving Eq

data ShowExpr t e
  = ShowLit { _repr :: t }
  | Prefix  { _repr :: t, _assoc :: (Int,Side), _child  :: e }
  | Postfix { _repr :: t, _assoc :: (Int,Side), _child  :: e }
  | Binary  { _repr :: t, _assoc :: (Int,Side), _lchild :: e
                                              , _rchild :: e }
  deriving Functor
  
makeLenses ''ShowExpr
```

The lenses are probably overkill. For printing, we need not only the precedence of the current level, but also the precedence one level below. Seems like the perfect case for a zygomorphism:

```{.haskell}
showExprAlg :: Semigroup t
            => (t -> t)
            -> ShowExpr t (Maybe (Int,Side), t)
            -> t
showExprAlg prns = \case 
    ShowLit t               ->                   t
    Prefix  t s       (q,y) ->                   t <> ifPrns R s q y
    Postfix t s (p,x)       -> ifPrns L s p x <> t
    Binary  t s (p,x) (q,y) -> ifPrns L s p x <> t <> ifPrns R s q y
  where
    ifPrns sid (op,oa) (Just (ip,ia))
      | ip < op || ip == op && (ia /= oa || sid /= oa) = prns
    ifPrns _ _ _ = id
```

The first argument to this algebra is the parenthesizing function. This algebra works fine for when the `ShowExpr`{.haskell} type is already constructed:

```{.haskell}
showExpr' :: Semigroup t => (t -> t) -> Fix (ShowExpr t) -> t
showExpr' = zygo (preview assoc) . showExprAlg
```

But we still need to construct the `ShowExpr`{.haskell} from something else first. `hylo`{.haskell} might be a good fit:

```{.haskell}
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
```

But that performs a catamorphism after an anamorphism, and we want a zygomorphism after an anamorphism. Luckily, the [recursion-schemes](https://hackage.haskell.org/package/recursion-schemes) library is constructed in such a way that different schemes can be stuck together relatively easily:

```{.haskell}
hylozygo
    :: Functor f
    => (f a -> a) -> (f (a, b) -> b) -> (c -> f c) -> c -> b
hylozygo x y z = ghylo (distZygo x) distAna y (fmap Identity . z)

showExpr :: Semigroup t
         => (t -> t)
         -> (e -> ShowExpr t e)
         -> e -> t
showExpr = hylozygo (preview assoc) . showExprAlg
```

Let's try it out, with a right-associative operator this time to make things more difficult:

```{.haskell}
data ExprF a
  = LitF Integer
  | (:+:) a a
  | (:*:) a a
  | (:^:) a a
  deriving Functor

makeHandler ''ExprF

newtype Expr = Expr { runExpr :: ExprF Expr }

instance Num Expr where
  fromInteger = Expr . LitF
  x + y = Expr (x :+: y)
  x * y = Expr (x :*: y)
  
infixr 8 ^*
(^*) :: Expr -> Expr -> Expr
x ^* y = Expr (x :^: y)

instance Show Expr where
  show =
    showExpr
      (\x -> "(" ++ x ++ ")")
      (index ExprFAlg {..} . runExpr)
    where
      litF = ShowLit . show
      (+:) = Binary " + " (6,L)
      (*:) = Binary " * " (7,L)
      (^:) = Binary " ^ " (8,R)
```

Since we only specified `Semigroup`{.haskell} in the definition of `showExpr`{.haskell}, we can use the more efficient difference-list definition of `Show`{.haskell}:

```{.haskell}
instance Show Expr where
    showsPrec _ =
      appEndo . showExpr
        (Endo . showParen True . appEndo)
        (index ExprFAlg {..} . runExpr)
      where
        litF = ShowLit . Endo . shows
        (+:) = Binary (Endo (" + " ++)) (6,L)
        (*:) = Binary (Endo (" * " ++)) (7,L)
        (^:) = Binary (Endo (" ^ " ++)) (8,R)

1 ^* 2 ^* 3         -- 1 ^ 2 ^ 3
(1 ^* 2) ^* 3       -- (1 ^ 2) ^ 3
1 * 2 + 3   :: Expr -- 1 * 2 + 3
1 * (2 + 3) :: Expr -- 1 * (2 + 3)
```
