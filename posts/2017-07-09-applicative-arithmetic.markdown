---
title: Applicative Arithmetic
tags: Haskell
---

# Safer Arithmetic

There are a couple partial functions in the Haskell Prelude which people seem to agree shouldn't be there. `head`{.haskell}, for example, will throw an error on an empty list. Most seem to agree that it should work something more like this:

```{.haskell}
head :: Foldable f => f a -> Maybe a
head = foldr (const . Just) Nothing
```

There are other examples, like `last`{.haskell}, `!!`{.haskell}, etc.

One which people *don't* agree on, however, is division by zero. In the current Prelude, the following will throw an error:

```{.haskell}
1 / 0
```

The "safe" version might have a signature like this:

```{.haskell}
(/) :: Fractional a => a -> a -> Maybe a
```

However, this turns out to be quite a headache for writing code generally. So the default is the (somewhat) unsafe version.

Is there a way to introduce a safer version without much overhead, so the programmer is given the option? Of course! With some newtype magic, it's pretty simple to write a wrapper which catches division by zero in some arbitrary monad:

```{.haskell}
newtype AppNum f a = AppNum
    { runAppNum :: f a
    } deriving (Functor,Applicative,Monad,Alternative,Show,Eq,MonadFail)

instance (Num a, Applicative f) =>
         Num (AppNum f a) where
    abs = fmap abs
    signum = fmap signum
    (+) = liftA2 (+)
    (*) = liftA2 (*)
    (-) = liftA2 (-)
    negate = fmap negate
    fromInteger = pure . fromInteger

instance (Fractional a, MonadFail f, Eq a) =>
         Fractional (AppNum f a) where
    fromRational = pure . fromRational
    xs / ys =
        ys >>=
        \case
            0 -> fail "divide by zero"
            y -> fmap (/ y) xs
```

I'm using the `-XLambdaCase`{.haskell} extension and `MonadFail`{.haskell} here.

# Free Applicatives

You'll notice that you only need `Applicative`{.haskell} for most of the arithmetic operations above. In fact, you only need `Monad`{.haskell} when you want to examine the contents of `f`{.haskell}. Using that fact, we can manipulate expression trees using the free applicative from the [free](https://hackage.haskell.org/package/free) package. Say, for instance, we want to have free variables in our expressions. Using `Either`{.haskell}, it's pretty easy:

```{.haskell}
type WithVars = AppNum (Ap (Either String)) Integer

var :: String -> WithVars
var = AppNum . liftAp . Left
```

We can collect the free variables from an expression:

```{.haskell}
vars :: WithVars -> [String]
vars = runAp_ (either pure (const [])) . runAppNum

x = 1 :: WithVars
y = var "y"
z = var "z"

vars (x + y + z) -- ["y","z"]
```

If we want to sub in, though, we're going to run into a problem: we can't just pass in a `Map String Integer`{.haskell} because you're able to construct values like this:

```{.haskell}
bad :: AppNum (Ap (Either String)) (Integer -> Integer -> Integer)
bad = AppNum (liftAp (Left "oh noes"))
```

We'd need to pass in a `Map String (Integer -> Integer -> Integer)`{.haskell} as well; in fact you'd need a map for every possible type. Which isn't feasible.

# GADTs

Luckily, we *can* constrain the types of variables in our expression so that they're always `Integer`{.haskell}, using a GADT:

```{.haskell}
data Variable a where
        Constant :: a -> Variable a
        Variable :: String -> Variable Integer
```

The type above seems useless on its own: it doesn't have a `Functor`{.haskell} instance, never mind an `Applicative`{.haskell}, so how can it fit into `AppNum`{.haskell}?

The magic comes from the free applicative, which converts any type of kind `Type -> Type`{.haskell} into an applicative. With that in mind, we can change around the previous code:

```{.haskell}
type WithVars = AppNum (Ap Variable) Integer

var :: String -> WithVars
var = AppNum . liftAp . Variable

vars :: WithVars -> [String]
vars = runAp_ f . runAppNum
  where
    f :: Variable a -> [String]
    f (Constant _) = []
    f (Variable s) = [s]
```

And write the function to sub in for us:

```{.haskell}
variable
    :: Applicative f
    => (String -> f Integer) -> Variable a -> f a
variable _ (Constant x) = pure x
variable f (Variable s) = f s

replace :: Map String Integer -> WithVars -> Integer
replace m = runIdentity . runAp (variable (pure . (m Map.!))) . runAppNum

replace (Map.fromList [("z",2), ("y",3)]) (x + y + z)
-- 6
```

# Accumulation

This will fail if a free variable isn't present in the map, unfortunately. To fix it, we *could* use `Either`{.haskell} instead of `Identity`{.haskell}:

```{.haskell}
replace :: Map String Integer -> WithVars -> Either String Integer
replace m =
    runAp
        (variable $
         \s ->
              maybe (Left s) Right (Map.lookup s m)) .
    runAppNum
```

But this only gives us the first missing variable encountered. We'd like to get back *all* of the missing variables, ideally: accumulating the `Left`{.haskell}s. `Either`{.haskell} doesn't accumulate values, as if it did it would [break the monad laws](https://stackoverflow.com/a/23611068/4892417).

There's no issue with the *applicative* laws, though, which is why the [validation](https://hackage.haskell.org/package/validation-0.5.4) package provides a *non-monadic* either-like type, which we can use here.

```{.haskell}
replace :: Map String Integer -> WithVars -> AccValidation [String] Integer
replace m =
    runAp
        (variable $
         \s ->
              maybe (AccFailure [s]) pure (Map.lookup s m)) .
    runAppNum

replace (Map.fromList []) (x + y + z)
-- AccFailure ["y","z"]
```

# Other uses

There are a bunch more applicatives you could use instead of `Either`{.haskell}. Using lists, for instance, you could calculate the possible outcomes from a range of inputs:

```{.haskell}
range :: WithVars -> [Integer]
range = runAp (variable (const [1..3])) . runAppNum

range (x + y + z)
-- [3,4,5,4,5,6,5,6,7]
```

Or you could ask the user for input:

```{.haskell}
query :: WithVars -> IO Integer
query = runAp (variable f) . runAppNum
  where
    f s = do
      putStr "Input a value for "
      putStrLn s
      fmap read getLine
```

Finally, and this one's a bit exotic, you could examine every variable in turn, with defaults for the others:

```{.haskell}
zygo
    :: Applicative g
    => (forall x. f x -> g x)
    -> (forall x. f x -> g (x -> a) -> b)
    -> Ap f a
    -> [b]
zygo (l :: forall x. f x -> g x) (c :: forall x. f x -> g (x -> a) -> b) =
    fst . go (pure id)
  where
    go
        :: forall c.
           g (c -> a) -> Ap f c -> ([b], g c)
    go _ (Pure x) = ([], pure x)
    go k (Ap x f) = (c x (liftA2 (.) k ls) : xs, lx <**> ls)
      where
        (xs,ls) = go (liftA2 (flip (.) . flip id) lx k) f
        lx = l x

examineEach :: WithVars -> [Integer -> Integer]
examineEach = zygo (variable (const (pure 1))) g . runAppNum
  where
    g :: Variable a -> (Integer -> (a -> b)) -> Integer -> b
    g (Constant x) rhs = ($x) <$> rhs
    g (Variable _) rhs =
        \i ->
             rhs i i
```

This produces a list of functions which are equivalent to subbing in for each variable with the rest set to 1.
