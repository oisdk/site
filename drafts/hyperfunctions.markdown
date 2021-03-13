---
title: Hyperfunctions
tags: Haskell
bibliography: Hyperfunctions.bib
---

Check out this type:

```haskell
newtype a -&> b = Hyp { invoke :: (b -&> a) -> b } 
```

I came across it a few months ago, and for my money it's the most
interesting newtype you can write in Haskell.
The theory behind it is pretty mind-bending and fascinating, but even more
surprisingly it has some practical uses in optimisation.
Let's find out about it!

Values of the type `a -&> b` are called *hyperfunctions*
[@launchbury_coroutining_2013; -@launchbury_zip_2000; -@krstic_category_2000].
If we expand it out a bit we can see that it's an infinitely left-nested
function, which takes in some `a`s and returns some `b`s---kind of.

```haskell
type a -&> b = (b -&> a) -> b
             = ((a -&> b) -> a) -> b
             = (((b -&> a) -> b) -> a) -> b
             = ((((... -> b) -> a) -> b) -> a) -> b
```

By "takes in some `a`s" I mean it takes in a function which *returns* an `a`.
That function, in turn, takes in something which returns a `b`, which takes in
something which returns an `a`, and so on.
So all of the `a`s end up in negative positions, and all of the `b`s in
positive.
"Positivity" here refers to the position relative to the arrows:
to the left of an arrow is negative, to the right is positive, but two negatives
cancel out (if you think about it, a function of type `(a -> b) -> c` will have
to produce, not consume, an `a`).

# Hyperfunctions Are Useful

So I mentioned that hyperfunctions show up if you're doing relatively practical
optimisations in Haskell: that's actually where I first came across them.
If you look hard enough, hyperfunctions show up *everywhere* in optimisation
code.

In a [previous post](2020-08-22-some-more-list-algorithms.html) I showed a
function which allows you to fuse away `zip` on both parameters: 

```haskell
newtype Zip a b = 
  Zip { runZip :: a -> (Zip a b -> b) -> b }

zip :: forall a b. [a] -> [b] -> [(a,b)]
zip xs ys = xz yz
  where
    xz :: Zip a [(a,b)] -> [(a,b)]
    xz = foldr f b xs
      where    
        f x xk yk = runZip yk x xk
        b _ = []
    
    yz :: Zip a [(a,b)]
    yz = foldr f b ys
      where
        f y yk = Zip (\x xk -> (x,y) : xk yk)
        b = Zip (\_ _ -> [])
```

It turns out that this `Zip` type is just a hyperfunction in disguise (with some
parameters flipped around):

```haskell
zip :: forall a b. [a] -> [b] -> [(a,b)]
zip xs ys = invoke xz yz
  where
    xz :: (a -> [(a,b)]) -&> [(a,b)]
    xz = foldr f b xs
      where
        f x xk = Hyp (\yk -> invoke yk xk x)    
        b = Hyp (\_ -> [])
    
    yz :: [(a,b)] -&> (a -> [(a,b)]) 
    yz = foldr f b ys
      where
        f y yk = Hyp (\xk x -> (x,y) : invoke xk yk)
        b = Hyp (\_ _ -> [])
```

Similarly, in [another previous
post](2019-05-14-corecursive-implicit-queues.html) I wrote about an "implicit
corecursive queue", which you could use for writing breadth-first traversals of
trees:

```haskell
data Tree a = a :& [Tree a]

newtype Q a = Q { q :: (Q a -> [a]) -> [a] }

bfenum :: Tree a -> [a]
bfenum t = q (f t b) e
  where
    f :: Tree a -> Q a -> Q a
    f (x :& xs) fw = Q (\bw -> x : q fw (bw . flip (foldr f) xs))
    
    b :: Q a
    b = fix (Q . flip id)
    
    e :: Q a -> [a]
    e = fix (flip q)
```

Again, `Q` here is another hyperfunction!

```haskell
bfenum :: Tree a -> [a]
bfenum t = invoke (f t e) e
  where
    f :: Tree a -> ([a] -&> [a]) -> ([a] -&> [a])
    f (x :& xs) fw = Hyp (\bw -> x : invoke fw (Hyp (invoke bw . flip (foldr f) xs)))
    
    e :: [a] -&> [a]
    e = Hyp (\k -> invoke k e)
```

One of the problems I had with the above function was that it didn't terminate:
it could enumerate all the elements of the tree but it didn't know when to stop.
A similar program [@allison_circular_2006; described and translated to Haskell
in @smith_lloyd_2009] manages to solve the problem with a counter.
Will it shock you to find out this solution can also be encoded with a
hyperfunction?

```haskell
bfenum t = invoke (f t e) e 1
  where
    f :: Tree a -> (Int -> [a]) -&> (Int -> [a]) 
                -> (Int -> [a]) -&> (Int -> [a])
    f (x :& xs) fw =
      Hyp (\bw n -> x :
            invoke fw
              (Hyp (invoke bw . flip (foldr f) xs)) (n+1))

    e :: (Int -> [a]) -&> (Int -> [a])
    e = Hyp b
    
    b x 0 = []
    b x n = invoke x (Hyp b) (n-1)
```

(my version here is actually a good bit different from the one in
@smith_lloyd_2009, but the basic idea is the same)

It does annoy me a little that this program contains a numeric counter: we can
do the same job with `Maybe` if we define a kind of "hyperfunction transformer"
thing:

```haskell
newtype HypM m a b = HypM { invokeM :: (m (HypM m a b) -> a) -> b }

bfenum t = r (f t e)
  where
    f :: Tree a -> HypM Maybe [a] [a] -> HypM Maybe [a] [a]
    f (x :& xs) fw = HypM (\bw -> x : invokeM fw (bw . Just . flip (foldr f) xs . fromMaybe e))

    e :: HypM Maybe [a] [a]
    e = HypM ($ Nothing)
    
    r :: HypM Maybe [a] [a] -> [a]
    r = fix (flip invokeM . maybe [])
```

This version of hyperfunctions with the `m` parameter can actually be used to
write some monadic versions of the functions we already have.
There is, for instance, a church-encoded version of the `ListT` monad
transformer: 

```haskell
newtype ListT m a = ListT { runListT :: forall b. (a -> m b -> m b) -> m b -> m b }
```

The `HypM` type allows us to write an $\mathcal{O}(n)$ `zip` on this type:

```haskell
liftA2M :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
liftA2M f xs ys = do
  x <- xs
  y <- ys
  f x y

zipM :: Monad m => ListT m a -> ListT m b -> ListT m (a,b)
zipM xs ys = ListT (\c n -> 
  let
    xf x xk = pure (HypM (\yk -> yk xk x))
    xb = pure (HypM (\_ -> n))

    yf y yk = pure (\xk x -> c (x, y) (liftA2M invokeM xk yk))
    yb = pure (\_ _ -> n)
  in liftA2M invokeM (runListT xs xf xb) (runListT ys yf yb))
```

This function actually allows you to cut several functions on
[`LogicT`](https://hackage.haskell.org/package/logict-0.7.1.0/docs/Control-Monad-Logic.html#g:2)
from $\mathcal{O}(n^2)$ (or worse) to $\mathcal{O}(n)$ (I think).

The last place I can think of that I've seen hyperfunctions show up is in
coroutine implementations.
The `ProdPar` and `ConsPar` types from @pieters_faster_2019 are good examples:

```haskell
newtype ProdPar a b = ProdPar (ConsPar a b -> b) 
newtype ConsPar a b = ConsPar (a -> ProdPar a b -> b)
```

`ProdPar a b` is isomorphic to `(a -> b) -&> b`, and `ConsPar a b` to `b -&> (a
-> b)`, as witnessed by the following functions:

```haskell
fromP :: ProdPar a b -> (a -> b) -&> b
fromP (ProdPar x) = Hyp (x . toC)

toC ::  b -&> (a -> b) -> ConsPar a b
toC (Hyp h) = ConsPar (\x p -> h (fromP p) x)

toP :: (a -> b) -&> b -> ProdPar a b
toP (Hyp x) = ProdPar (x . fromC)

fromC :: ConsPar a b -> b -&> (a -> b)
fromC (ConsPar p) = Hyp (\h x -> p x (toP h))
```

In fact this reveals a little about what was happening in the `zip` function: we
convert the left-hand list to a `ProdPar` (producer), and the right-hand to a
consumer, and apply them to each other.

# Hyperfunctions Don't Exist in Set Theory

Aside from just being kind of weird intuitively, hyperfunctions are weird *in
theory*.
Set-theoretically, for instance, you cannot form the set of `a -&> b`: if you
tried, you'd run into those pesky size restrictions which stop us from making
things like "the set of all sets".
Haskell types, however, are not sets, precisely because we can define things
like `a -&> b`.

# Hyperfunctions Don't Exist in (pedantic) Type Systems

For slightly different reasons to the set theory restrictions, we can't define
the type of hyperfunctions in Agda.
The following will get an error:

```agda
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inductive; constructor hyp
  field invoke : (B ↬ A) → B
```

And for good reason!
Agda doesn't allow recursive types where the recursive call is in a negative
position.
If we turn off the positivity checker, we can write Curry's paradox (example
proof taken from [here](https://stackoverflow.com/a/51253757/4892417)):

```agda
yes? : ⊥ ↬ ⊥
yes? .invoke h = h .invoke h

no! : (⊥ ↬ ⊥) → ⊥
no! h = h .invoke h

boom : ⊥
boom = no! yes?
```

Note that this isn't an issue with the termination checker: 
the above example passes all the normal termination conditions without issue
(yes, even if `↬` is marked as `coinductive`).
It's directly because the type itself is not positive.

Interestingly, there is a slightly different, and nearly equivalent, definition
of hyperfunctions which doesn't allow us to write the above proof:

```agda
record _↬_ (A : Type a) (B : Type b) : Type (a ℓ⊔ b) where
  inductive; constructor hyp
  field invoke : ((A ↬ B) → A) → B
```

This is basically a slightly expanded out version of the hyperfunction type, and
importantly it's *positive*.
Not *strictly* positive however, since the recursive call does occur to the left
of a function arrow: it's just positive, in that it's to the left of an even
number of function arrows.

I found in a blog post by @sjoberg_why_2015 some interesting discussion
regarding the question of this extra strictness: in Coq, allowing certain
positive but not *strictly* positive types does indeed introduce an
inconsistency [@coquand_inductively_1990].
However this inconsistency relies on an impredicative universe, which Agda
doesn't have.
As far as I understand it, it would likely be safe to allow types like `↬` above
in Agda [@coquand_agda_2013], although I'm not certain that with all of Agda's newer
features that's still the case.

