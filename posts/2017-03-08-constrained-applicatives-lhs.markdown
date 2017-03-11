---
title: Constrained Applicatives
tags: Haskell
bibliography: Restricted Monads.bib
---

In Haskell restricted monads are monads which can't contain every type. `Set`{.haskell} is a good example. If you look in the documentation for [Data.Set](https://hackage.haskell.org/package/containers-0.5.10.1/docs/Data-Set.html) you'll see several functions which correspond to functions in the Functor/Applicative/Monad typeclass hierarchy:

```{.haskell}
map :: Ord b => (a -> b) -> Set a -> Set b
singleton :: a -> Set a
foldMap :: Ord b => (a -> Set b) -> Set a -> Set b -- specialized
```

Unfortunately, though, `Set`{.haskell} can't conform to `Functor`{.haskell}, because the signature of `fmap`{.haskell} looks like this:

```{.haskell}
fmap :: Functor f => (a -> b) -> f a -> f b
```

It doesn't have an `Ord`{.haskell} constraint.

This is annoying: when using `Set`{.haskell}, lots of things have to be imported qualified, and you have to remember the slightly different names of extra functions like `map`{.haskell}. More importantly, you've lost the ability to write generic code over `Functor`{.haskell} or `Monad`{.haskell} which will work on `Set`{.haskell}.

There are a number of ways to get around this problem. [Here](http://okmij.org/ftp/Haskell/set-monad.html#set-cps), an approach using reflection-reification is explored. These are the types involved:

```{.haskell}
newtype SetC a = 
       SetC{unSetC :: forall r. Ord r => (a -> Set r) -> Set r}

reifySet :: Ord r => SetC r -> Set r
reifySet m = unSetC m singleton

reflectSet :: Ord r => Set r -> SetC r
reflectSet s = SetC $ \k -> S.foldr (\x r -> k x `union` r) S.empty s
```

`SetC`{.haskell} is just `Cont`{.haskell} in disguise. In fact, we can generalize this pattern, using Constraint Kinds:

```{.haskell}
newtype FreeT c m a = 
       FreeT { runFreeT :: forall r. c r => (a -> m r) -> m r}

reifySet :: Ord a => FreeT Ord Set a -> Set a
reifySet m = runFreeT m singleton

reflectSet :: Set r -> FreeT Ord Set r
reflectSet s = FreeT $ \k -> S.foldr (\x r -> k x `union` r) S.empty s
```

`FreeT`{.haskell} looks an *awful lot* like `ContT`{.haskell} by now. The type has some other interesting applications, though. For instance, this type:

```{.haskell}
type FM = FreeT Monoid Identity
```

Is the free monoid. If we use a transformers-style type synonym, the naming becomes even nicer:

```{.haskell}
type Free c = FreeT c Identity

runFree :: c r => Free c a -> (a -> r) -> r
runFree xs f = runIdentity (runFreeT xs (pure . f))

instance Foldable (Free Monoid) where
  foldMap = flip runFree
```

Check out [this package](https://hackage.haskell.org/package/free-functors) for an implementation of the non-transformer `Free`{.haskell}.

## Different Classes

This is still unsatisfying, though. Putting annotations around your code feels inelegant. The next solution is to replace the monad class altogether with our own, and turn on `-XRebindableSyntax`{.haskell}. There are a few ways to design this new class. One option is to use [multi-parameter type classes](http://okmij.org/ftp/Haskell/types.html#restricted-datatypes). Another solution is with an associated type:

```{.haskell}
class Functor f where
  type Suitable f a :: Constraint
  fmap :: Suitable f b => (a -> b) -> f a -> f b
```

This is similar to the approach taken in the [rmonad](https://hackage.haskell.org/package/rmonad) library, except that library doesn't use constraint kinds (they weren't available when the library was made), so it has to make do with a `Suitable`{.haskell} class. Also, the signature for `fmap`{.haskell} in rmonad is:

```{.haskell}
fmap :: (Suitable f a, Suitable f b) => (a -> b) -> f a -> f b
```

I don't want to constrain `a`{.haskell}: I figure if you can get something *into* your monad, it *must* be suitable. And I really want to reduce the syntactic overhead of writing extra types next to your functions.

There's also the [supermonad](https://hackage.haskell.org/package/supermonad-0.1/docs/Control-Supermonad-Constrained.html) library out there which is much more general than any of these examples: it supports indexed monads as well as constrained.

Anyway,`Monad`{.haskell} is defined similarly to `Functor`{.haskell}:

```{.haskell}
class Functor m => Monad m where
  return :: Suitable m a => a -> m a
  (>>=) :: Suitable m b => m a -> (a -> m b) -> m b
```

Again, I want to minimize the use of `Suitable`{.haskell}, so for `>>=`{.haskell} there's only a constraint on `b`{.haskell}.

Finally, here's the `Set`{.haskell} instance:

```{.haskell}
instance Functor Set where
    type Suitable Set a = Ord a
    fmap = Set.map
```

## Monomorphic

With equality constraints, you can actually make *monomorphic* containers conform to these classes (or, at least, wrappers around them).

```{.haskell}
import qualified Data.Text as Text

data Text a where
  Text :: Text.Text -> Text Char

instance Functor Text where
  type Suitable Text a = a ~ Char
  fmap f (Text xs) = Text (Text.map f xs)
```

This pattern can be generalized with some more GADT magic:

```{.haskell}
data Monomorphic xs a b where
        Monomorphic :: (a ~ b) => xs -> Monomorphic xs a b

instance (MonoFunctor xs, a ~ Element xs) => Functor (Monomorphic xs a) where
  type Suitable (Monomorphic xs a) b = a ~ b
  fmap f (Monomorphic xs) = Monomorphic (omap f xs)
```

Where `omap`{.haskell} comes from the [mono-traversable](https://hackage.haskell.org/package/mono-traversable) package. You could go a little further, to `Foldable`{.haskell}:

```{.haskell}
instance (MonoFoldable xs, element ~ Element xs) =>
         Foldable (Monomorphic xs element) where
    foldr f b (Monomorphic xs) = ofoldr f b xs
    foldMap f (Monomorphic xs) = ofoldMap f xs
    foldl' f b (Monomorphic xs) = ofoldl' f b xs
    toList (Monomorphic xs) = otoList xs
    null (Monomorphic xs) = onull xs
    length (Monomorphic xs) = olength xs
    foldr1 f (Monomorphic xs) = ofoldr1Ex f xs
    elem x (Monomorphic xs) = oelem x xs
    maximum (Monomorphic xs) = maximumEx xs
    minimum (Monomorphic xs) = minimumEx xs
    sum (Monomorphic xs) = osum xs
    product (Monomorphic xs) = oproduct xs
```

## Back to normal

Changing the `FreeT`{.haskell} type above a little, we can go back to normal functors and monads, and write more general reify and reflect functions:

```{.haskell}
newtype FreeT m a = 
       FreeT { runFreeT :: forall r. Suitable m r => (a -> m r) -> m r}
       
reify :: (Monad m, Suitable m a) => FreeT m a -> m a
reify = flip runFreeT return

reflect :: Monad m => m a -> FreeT m a
reflect x = FreeT (x >>=)
```

So now our types, when wrapped, can conform to the Prelude's `Functor`{.haskell}. It would be nice if this type could be written like so:

```{.haskell}
reify :: Monad m => FreeT (Suitable m) m a -> m a
reify = flip runFreeT return

reflect :: Monad m => m a -> FreeT (Suitable m) m a
reflect x = FreeT (x >>=)
```

But unfortunately type families cannot be partially applied.

## Applicatives

The classes above aren't very modern: they're missing applicative. This one is tricky:

```{.haskell}
class Functor f => Applicative f where
  pure :: Suitable a => a -> f a
  (<*>) :: Suitable f b => f (a -> b) -> f a -> f b
```

The issue is `f (a -> b)`{.haskell}. There's no *way* you're getting some type like that into `Set`{.haskell}. This means that `<*>`{.haskell} is effectively useless. No problem, you think: define `liftA2`{.haskell} instead:

```{.haskell}
class Functor f => Applicative f where
  pure :: Suitable a => a -> f a
  liftA2 :: Suitable f c => (a -> b -> c) -> f a -> f b -> f c

(<*>) :: (Applicative f, Suitable f b) => f (a -> b) -> f a -> f b
(<*>) = liftA2 ($)
```

Great! Now we can use it with set. However, there's no way (that I can see) to define the other lift functions: `liftA3`{.haskell}, etc. Of course, if `>>=`{.haskell} is available, it's as simple as:

```{.haskell}
liftA3 f xs ys zs = do
  x <- xs
  y <- ys
  z <- zs
  pure (f x y z)
```

But now we can't define it for non-monadic applicatives (square matrices, ZipLists, etc.). This also forces us to use `>>=`{.haskell} when `<*>`{.haskell} [may have been more efficient](https://simonmar.github.io/posts/2015-10-20-Fun-With-Haxl-1.html).

The functions we're interested in defining look like this:

```{.haskell}
liftA2 :: Suitable f c => (a -> b -> c) -> f a -> f b -> f c
liftA3 :: Suitable f d => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA4 :: Suitable f e => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
```

There's a clear pattern, but no obvious way to abstract over it. Type-level shenanigans to the rescue!

The pattern might be expressed like this:

```{.haskell}
liftA :: Func args -> Func lifted args
```

We can store these types as heterogeneous lists:

```{.haskell}
infixr 5 :-
data Vect xs where
  Nil  :: Vect '[]
  (:-) :: x -> Vect xs -> Vect (x ': xs)

infixr 5 :*
data AppVect f xs where
  NilA :: AppVect f '[]
  (:*) :: f x -> AppVect f xs -> AppVect f (x ': xs)
```

And `liftA`{.haskell} can be represented like this:

```{.haskell}
liftA
    :: Suitable f b
    => (Vect xs -> b) -> AppVect f xs -> f b

liftA2
    :: Suitable f c
    => (a -> b -> c) -> f a -> f b -> f c
liftA2 f xs ys =
    liftA
        (\(x :- y :- Nil) ->
              f x y)
        (xs :* ys :* NilA)

liftA3
    :: Suitable f d
    => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3 f xs ys zs =
    liftA
        (\(x :- y :- z :- Nil) ->
              f x y z)
        (xs :* ys :* zs :* NilA)

```

Cool! For unrestricted applicatives, we can define `liftA`{.haskell} in terms of `<*>`{.haskell}:

```{.haskell}
liftAP :: (Prelude.Applicative f) 
       => (Vect xs -> b) -> (AppVect f xs -> f b)
liftAP f NilA = Prelude.pure (f Nil)
liftAP f (x :* NilA) 
  = Prelude.fmap (f . (:-Nil)) x
liftAP f (x :* xs) 
  =  ((f .) . (:-)) Prelude.<$> x Prelude.<*> liftAP id xs
```

And for types with a monad instance, we can define it in terms of `>>=`{.haskell}:

```{.haskell}
liftAM :: (Monad f, Suitable f b) 
       => (Vect xs -> b) -> (AppVect f xs -> f b)
liftAM f NilA = pure (f Nil)
liftAM f (x :* NilA) = fmap (f . (:-Nil)) x
liftAM f (x :* xs) = x >>= \y -> liftAM (f . (y:-)) xs
```

## Efficiency

This approach is *really* slow. Every function wraps up its arguments in a `Vect`{.haskell}, and it's just generally awful.

What about *not* wrapping up the function? Type families can help here:

```{.haskell}
type family FunType (xs :: [*]) (y :: *) :: * where
  FunType '[] y = y
  FunType (x ': xs) y = x -> FunType xs y
```

It gets really difficult to define `liftA`{.haskell} using `<*>`{.haskell} now, though. `liftAM`{.haskell}, on the other hand, is a breeze:

```{.haskell}
liftAM :: Monad f => FunType xs a -> AppVect f xs -> f a
liftAM f Nil = pure f
liftAM f (x :< xs) = x >>= \y -> liftAM (f y) xs
```

And no vector constructors on the right of the bind!

Still, no decent definition using `<*>`{.haskell}. The problem is that we're using a cons-list to represent a function's arguments, but `<*>`{.haskell} is left-associative, so it builds up arguments as a snoc list. Lets try using a snoc-list as the type family:

```{.haskell}
infixl 5 :>
data AppVect f xs where
  Nil :: AppVect f '[]
  (:>) :: AppVect f xs -> f x -> AppVect f (x ': xs)

type family FunType (xs :: [*]) (y :: *) :: * where
  FunType '[] y = y
  FunType (x ': xs) y = FunType xs (x -> y)

liftA
    :: Suitable f a
    => FunType xs a -> AppVect f xs -> f a
```

`liftAP`{.haskell} now gets a natural definition:

```{.haskell}
liftAP :: Prelude.Applicative f => FunType xs a -> AppVect f xs -> f a
liftAP f Nil = Prelude.pure f
liftAP f (Nil :> xs) = Prelude.fmap f xs
liftAP f (ys :> xs) = liftAP f ys Prelude.<*> xs
```

But what about `liftAM`{.haskell}? It's much more difficult, fundamentally because `>>=`{.haskell} builds up arguments as a cons-list. To convert between the two efficiently, we need to use the trick for reversing lists efficiently: build up the reversed list as you go.

```{.haskell}
liftAM :: (Monad f, Suitable f a) => FunType xs a -> AppVect f xs -> f a
liftAM = go pure where
  go :: (Suitable f b, Monad f) 
     => (a -> f b) -> FunType xs a -> AppVect f xs -> f b
  go f g Nil = f g
  go f g (xs :> x) = go (\c -> x >>= f . c) g xs
```

Using these definitions, we can make `Set`{.haskell}, `Text`{.haskell}, and all the rest of them applicatives, while preserving the applicative operations. Also, from my preliminary testing, there seems to be *no* overhead in using these new definitions for `<*>`{.haskell}.

## Normalized Embedding

In @sculthorpe_constrained-monad_2013, there's discussion of this type:

```{.haskell}
data NM :: (* -> Constraint) -> (* -> *) -> * -> * where
  Return :: a -> NM c t a
  Bind :: c x => t x -> (x -> NM c t a) -> NM c t a
```

This type allows constrained monads to become normal monads. It can be used for the same purpose as the `FreeT`{.haskell} type from above. In the paper, the free type is called `RCodT`{.haskell}.

One way to look at the type is as a concrete representation of the monad class, with each method being a constructor.

You might wonder if there are similar constructs for functor and applicative. Functor is simple:

```{.haskell}
data NF :: (* -> Constraint) -> (* -> *) -> * -> * where
  FMap :: c x => (x -> a) -> t x -> NF c t a
```

Again, this can conform to functor (and *only* functor), and can be interpreted when the final type is `Suitable`{.haskell}.

Like above, it has a continuation version, [Yoneda](https://hackage.haskell.org/package/kan-extensions-5.0.1/docs/Data-Functor-Yoneda.html).

For applicatives, though, the situation is different. In the paper, they weren't able to define a transformer for applicatives that could be interpreted in some restricted applicative. I needed one because I wanted to use `-XApplicativeDo`{.haskell} notation: the desugaring uses `<*>`{.haskell}, not the `liftAn`{.haskell} functions, so I wanted to construct a free applicative using `<*>`{.haskell}, and run it using the lift functions. What I managed to cobble to gether doesn't *really* solve the problem, but it works for `-XApplicativeDo`!

The key with a lot of this was realizing that `<*>`{.haskell} is *snoc*, not cons. Using a [free applicative](https://ro-che.info/articles/2013-03-31-flavours-of-free-applicative-functors):

```{.haskell}
data Free f a where
  Pure :: a -> Free f a
  Ap :: Free f (a -> b) -> f a -> Free f b

instance Prelude.Functor (Free f) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Ap x y) = Ap ((f .) Prelude.<$> x) y

instance Prelude.Applicative (Free f) where
  pure = Pure
  Pure f <*> y = Prelude.fmap f y
  (Ap x y) <*> z = Ap (flip Prelude.<$> x Prelude.<*> z) y
```

This type can conform to `Applicative`{.haskell} and `Functor`{.haskell} no problem. And all it needs to turn back into a constrained applicative is for the outer type to be suitable:

```{.haskell}
lift :: f a -> Free f a
lift = Ap (Pure id)

lower
    :: forall f a c.
       Free f a
    -> (forall xs. FunType xs a -> AppVect f xs -> f c)
    -> f c
lower (Pure x) f = f x Nil
lower (Ap fs x :: Free f a) f =
    lower fs (\ft av -> f ft (av :> x))

lowerConstrained
    :: (Constrained.Applicative f, Suitable f a)
    => Free f a -> f a
lowerConstrained x = lower x liftA
```

There's probably a more efficient way to encode it, though.
