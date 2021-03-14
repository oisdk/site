---
title: Hyperfunctions
tags: Haskell
bibliography: Hyperfunctions.bib
---

Check out this type:

```haskell
newtype a -&> b = Hyp { invoke :: (b -&> a) -> b } 
```

This is the type of hyperfunctions [@launchbury_coroutining_2013;
-@launchbury_zip_2000; -@krstic_category_2000], and I think 
it's one of the weirdest and most interesting newtypes you can write in
Haskell.

The first thing to notice is that the recursion pattern is weird.
For a type to refer to itself recursively on the *left* of a function arrow is
pretty unusual, but on top of that the recursion here is *non-regular*.
That means that the recursive reference has different type parameters to its
parent: on the left-hand-side of the equals sign we have `a -&> b`, but on the
right we refer to `b -&> a`.

Being weird is reason enough to write about them, but what's really shocking
about hyperfunctions is that they're *useful*.
Once I saw the definition  I realised that a bunch of
optimisation code I had written (to fuse away zips in particular) was actually
using hyperfunctions [@ghani_monadic_2005].
After that, I saw them all over the place: in coroutine implementations, queues,
breadth-first traversals, etc.

Anyways, since coming across hyperfunctions a few months ago I thought I'd do a
writeup on them.
I'm kind of surprised they're not more well-known, to be honest: they're like a
slightly more enigmatic
[`Cont`](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html)
monad, with a far cooler name.
Let's get into it!

# What Are Hyperfunctions?

The newtype noise kind of hides what's going on with hyperfunctions:
expanding the definition out might make things slightly clearer.

```haskell
type a -&> b = (b -&> a) -> b
             = ((a -&> b) -> a) -> b
             = (((b -&> a) -> b) -> a) -> b
             = ((((... -> b) -> a) -> b) -> a) -> b
```

So a value of type `a -&> b` is kind of an infinitely left-nested function type.
One thing worth noticing is that all the `a`s are in negative positions and all
the `b`s in positive.
This negative and positive business basically refers to the position of
arguments in relation to a function arrow: to the left are negatives, and to
the right are positives, but two negatives cancel out.

```haskell
((((... -> b) -> a) -> b) -> a) -> b
           +     -     +     -     +
```

All the things in negative positions are kind of like the things a function
"consumes", and positive positions are the things "produced".
It's worth fiddling around with very nested function types to get a feel for
this notion.
For hyperfunctions, though, it's enough to know that `a -&> b` does indeed (kind
of) take in a bunch of `a`s, and it kind of produces `b`s.

By the way, one of the ways to get to grips with polarity in this sense is to
play around with the Cont monad, codensity monad, or selection monad
[@hedges_selection_2015].
If you do, you may notice one of the interesting parallels about hyperfunctions:
the type `a -&> a` is in fact the fixpoint of the continuation monad (`Fix (Cont
a)`).
Suspicious!

# Hyperfunctions Are Everywhere

Before diving further into the properties of the type itself, I'd like to give
some examples of how it can show up in pretty standard optimisation code.

### Zips


Let's say you wanted to write `zip` with `foldr` (I have already described this
particular algorithm in a [previous
post](2020-08-22-some-more-list-algorithms.html)).
Not `foldr` on the left argument, mind you, but `foldr` on *both*.
If you proceed mechanically, replacing every recursive function with `foldr`,
you can actually arrive at a definition:

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip xs ys = foldr xf xb xs (foldr yf yb ys)
  where
    xf x xk yk = yk x xk
    xb _ = []
    
    yf y yk x xk = (x,y) : xk yk
    yb _ _ = []
```

In an untyped language, such a definition would be totally fine.
In Haskell, though, the compiler will complain with the following:

```
• Occurs check: cannot construct the infinite type:
    t0 ~ a -> (t0 -> [(a, b)]) -> [(a, b)]
```

Seasoned Haskellers will know, though, that this is not a type error: no, this
is a type *recipe*.
The compiler is telling you what parameters it wants you to stick in the newtype:

```haskell
newtype Zip a b = 
  Zip { runZip :: a -> (Zip a b -> [(a,b)]) -> [(a,b)] }

zip :: forall a b. [a] -> [b] -> [(a,b)]
zip xs ys = xz yz
  where
    xz :: Zip a b -> [(a,b)]
    xz = foldr f b xs
      where    
        f x xk yk = runZip yk x xk
        b _ = []
    
    yz :: Zip a b
    yz = foldr f b ys
      where
        f y yk = Zip (\x xk -> (x,y) : xk yk)
        b = Zip (\_ _ -> [])
```

And here we see the elusive hyperfunction: hidden behind a slight change of
parameter order, `Zip a b` is in fact the same as `[(a,b)] -&> (a -> [(a,b)])`.

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

### BFTs

In [another previous post](2019-05-14-corecursive-implicit-queues.html) I
derived the following function to do a breadth-first traversal of a tree:

```haskell
data Tree a = a :& [Tree a]

newtype Q a = Q { q :: (Q a -> [a]) -> [a] }

bfe :: Tree a -> [a]
bfe t = q (f t b) e
  where
    f :: Tree a -> Q a -> Q a
    f (x :& xs) fw = Q (\bw -> x : q fw (bw . flip (foldr f) xs))
    
    b :: Q a
    b = Q (\k -> k b)
    
    e :: Q a -> [a]
    e (Q q) = q e
```

That `Q` type there is another hyperfunction.

```haskell
bfe :: Tree a -> [a]
bfe t = invoke (f t e) e
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
bfe t = invoke (f t e) e 1
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

### Coroutines

Hyperfunctions seem to me to be quite deeply related to coroutines.
At the very least several of the types involved in coroutine implementations are
actual hyperfunctions.
The `ProdPar` and `ConsPar` types from @pieters_faster_2019 are good examples:

```haskell
newtype ProdPar a b = ProdPar (ConsPar a b -> b) 
newtype ConsPar a b = ConsPar (a -> ProdPar a b -> b)
```

`ProdPar a b` is isomorphic to `(a -> b) -&> b`, and `ConsPar a b` to `b -&> (a
-> b)`, as witnessed by the following functions:

<details>
<summary>Conversion functions between `ProdPar`, `ConsPar` and hyperfunctions</summary>

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

</details>

In fact this reveals a little about what was happening in the `zip` function: we
convert the left-hand list to a `ProdPar` (producer), and the right-hand to a
consumer, and apply them to each other.


# Hyperfunctions Are Weird

Aside from just being kind of weird intuitively, hyperfunctions are weird *in
theory*.
Set-theoretically, for instance, you cannot form the set of `a -&> b`: if you
tried, you'd run into those pesky size restrictions which stop us from making
things like "the set of all sets".
Haskell types, however, are not sets, precisely because we can define things
like `a -&> b`.

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

The connection between non-strictly-positive types and breadth-first traversals
has been noticed before: @berger_martin_2019 make the argument for their
inclusion in Agda and Coq using a breadth-first traversal algorithm by
@hofmann_non_1993, which uses the following type:

```haskell
data Rou
  = Over
  | Next ((Rou -> [Int]) -> [Int])
```

Now this type *isn't* a hyperfunction (but it's close); we'll see soon what kind
of thing it is.

# Hyperfunctions Are a Category

So we've seen that hyperfunctions show up kind of incidentally through certain
optimisations, and we've seen that they occupy a strange space in terms of their
theoretical interpretation: we haven't yet seen much about the type itself in
isolation.
Luckily Ed Kmett has already written the [hyperfunctions
package](https://hackage.haskell.org/package/hyperfunctions)
-@kmett_hyperfunctions_2015, where a laundry list of instances are provided,
which can tell us a little more about what hyperfunctions can actually do on
their own.

The `Category` instance gives us the following:

```haskell
instance Category (-&>) where
  id = Hyp (\k -> invoke k id)
  f . g = Hyp (\k -> invoke f (g . k))
```

We've actually seen the identity function a few times: we used it as the base
case for recursion in the breadth-first traversal algorithms.

Composition we actually have used as well but it's more obscured.
An analogy to help clear things up is to think of hyperfunctions as a kind of
*stack*.
`id` is the empty stack, and we can use the following function to push items
onto the stack:

```haskell
push :: (a -> b) -> a -&> b -> a -&> b
push f q = Hyp (\k -> f (invoke k q))
```

Understood in this sense, composition acts like a zipping operation on stacks,
since we have the following law:

```haskell
push f p . push g q ≡ push (f . g) (p . q)
```

While we can't really pop elements off the top of the stack directly, we can
get close with `invoke`, since it satisfies the following law:

```haskell
invoke (push f p) q ≡ f (invoke q p)
```

Along with the `id` implementation we have, this will let us run a
hyperfunction, basically folding over the contents of the stack:

```haskell
run :: a -&> a -> a
run f = invoke f id
```

This analogy helps us understand how the breadth-first traversals worked: the
hyperfunctions are kind of like stacks with $\mathcal{O}(1)$ `push` and `zip`,
which is precisely what you need for an efficient breadth-first traversal.

```haskell
bfe :: Tree a -> [a]
bfe = run . f
  where
    f (x :& xs) = push (x:) (zips (map f xs))
    
    zips = foldr (.) id
```

Finally, hyperfunctions are of course monads:


```haskell
instance Monad ((-&>) a) where
  m >>= f = Hyp (\k -> invoke (f (invoke m (Hyp (invoke k . (>>=f))))) k)
```

I won't pretend to understand what's going on here, but it looks a little like a
nested reader monad.
Perhaps there's some intuition to be gained from noticing that `a -&> a ~ Fix
(Cont a)`.

# Hyper Arrows Are...?

As I said in the introduction I'm kind of surprised there's not more research
out there on hyperfunctions.
Aside from the excellent papers by @launchbury_coroutining_2013 there's just not
much out there.
Maybe it's that there's not that much theoretical depth to them, but all the
same there are some clear questions worth looking into.

For example: is there a hyperfunction monad transformer?
Or, failing that, can you thread a monad through the type at any point, and do
you get anything interesting out?

I have made a little headway on this question, while fiddling with one of the
`bfe` definitions above.
Basically I wanted to remove the `Int` counter for the terminating `bfe`, and I
wanted to use a `Maybe` somewhere instead.
I ended up generalising from `Maybe` to any `m`, yielding the following type:

```haskell
newtype HypM m a b = HypM { invokeM :: m ((HypM m a b -> a) -> b) }
```

This does the job for the breadth-first traversal:

```haskell
bfe t = r (f t e)
  where
    f :: Tree a -> HypM Maybe [a] [a] -> HypM Maybe [a] [a]
    f (x :& xs) fw = HypM (Just (\bw -> x : fromMaybe (\k -> k e) (invokeM fw) (bw . flip (foldr f) xs)))

    e :: HypM Maybe [a] [a]
    e = HypM Nothing
    
    r :: HypM Maybe [a] [a] -> [a]
    r = maybe [] (\k -> k r) . invokeM
```

(In fact, when `m` is specialised to `Maybe` we have the same type as `Rou`)

This type has a very practical use, as it happens, which is related to the
church-encoded list monad transformer:

```haskell
newtype ListT m a = ListT { runListT :: forall b. (a -> m b -> m b) -> m b -> m b }
```

Just like `-&>` allowed us to write `zip` on folds (i.e. using `foldr`), `HypM`
will allow us to write `zipM` on `ListT`:

```haskell
zipM :: Monad m => ListT m a -> ListT m b -> ListT m (a,b)
zipM xs ys = ListT (\c n ->
  let
    xf x xk = pure (\yk -> yk (HypM xk) x)
    xb = pure (\_ -> n)

    yf y yk = pure (\xk x -> c (x, y) (join (invokeM xk <*> yk)))
    yb = pure (\_ _ -> n)
  in join (runListT xs xf xb <*> runListT ys yf yb))
```

I actually think this function could be used to seriously improve the running
time of several of the functions on
[`LogicT`](https://hackage.haskell.org/package/logict-0.7.1.0/docs/Control-Monad-Logic.html#g:2):
my reading of them suggests that `interleave` is $\mathcal{O}(n^2)$ (or worse),
but the zip above could be trivially repurposed to give a $\mathcal{O}(n)$
`interleave`.
This would also have knock-on effects on, for instance, `>>-` and so on.

Another question is regarding the arrows of the hyperfunction.
We've seen that a hyperfunction kind of adds "stacking" to functions, can it do
the same for other arrows?
Basically, does the following type do anything useful?

```haskell
newtype HypP p a b = HypP { invokeP :: p (HypP p b a) b }
```

Along a similar vein, many of the breadth-first enumeration algorithms seem to
use "hyperfunctions over the endomorphism monoid".
Basically, they all produce hyperfunctions of the type `[a] -&> [a]`, and use
them quite similarly to how we would use difference lists.
But we know that there are Cayley transforms in other monoidal categories, for
instance in the applicative monoidal category: can we construct the
"hyperfunction" version of those?

-----

# References

