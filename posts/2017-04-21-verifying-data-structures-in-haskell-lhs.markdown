---
title: Verifying Data Structures in Haskell
bibliography: Data Structures.bib
---

A while ago I read [this](https://www.reddit.com/r/haskell/comments/63a4ea/fast_total_sorting_of_arbitrary_traversable/) post on reddit (by David Feuer), about sorting traversables, and I was inspired to write some pseudo-dependently-typed Haskell. The post (and subsequent [library](https://github.com/treeowl/sort-traversable)) detailed how to use size-indexed heaps to perform fast, total sorting on any traversable.

### Type-Level Numbers in Haskell

The normal representation of type-level natural numbers is [Peano](https://wiki.haskell.org/Peano_numbers) numbers:

```{.haskell}
data Nat = Z | S Nat
```

The terseness is pretty necessary here, unfortunately: arithmetic becomes unreadable otherwise. Regardless, `Z`{.haskell} stands for zero, and `S`{.haskell} for successor.

With the `-XDataKinds`{.haskell} extension, the above is automatically promoted to the type-level, as well as the value-level, so we can write type-level functions (type families) on the `Nat`{.haskell} type:

```{.haskell}
type family (+) (n :: Nat) (m :: Nat) :: Nat where
  Z + m = m
  S n + m = S (n + m)
```

The number of extensions turned on here is going to quickly get out of hand, so rather than enumerate each one as they come up, I'll just direct you to a repository with these examples at the end (quick aside: `-XUndecidableInstances`{.haskell} is *not* used at any point here, but more on that later). One pragma that's worth mentioning is:

```{.haskell}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}
```

Type-level code with a load of ticks can look pretty ugly, and the warnings aren't very helpful if you're doing a lot of type-level stuff. Watch out for `[]`{.haskell}, though: it always needs to be ticked to work properly.

### Using the Type-Level Numbers with a Pairing Heap

In the original post, a pairing heap [@fredman_pairing_1986] was used, for its simplicity and performance. The implementation looked like this:

```{.haskell}
data Heap n a where
  E :: Heap Z a
  T :: a -> HVec n a -> Heap (S n) a

data HVec n a where
  HNil :: HVec Z a
  HCons :: Heap m a -> HVec n a -> HVec (m + n) a
```

You immediately run into trouble when you try to define merge:

```{.haskell}
merge :: Ord a => Heap m a -> Heap n a -> Heap (m + n) a
merge E ys = ys
merge xs E = xs
merge h1@(T x xs) h2@(T y ys)
  | x <= y = T x (HCons h2 xs)
  | otherwise = T y (HCons h1 ys)
```

Three errors show up here, but we'll look at the first one: 

> `Could not deduce (m ~ (m + Z))`
    
GHC doesn't know that $x = x + 0$. Somehow, we'll have to *prove* that it does. The first attempt is going to use singletons.

### Singletons

If I were to prove the above in Idris, the proof would be as simple as this:

```{.idris}
plusZeroNeutral : (n : Nat) -> n + 0 = n
plusZeroNeutral Z = Refl
plusZeroNeutral (S k) = cong (plusZeroNeutral k)
```

We're able to use the language's normal function syntax to perform induction. In Haskell, on the other hand, it's a different story: the `+`{.haskell} function was defined in the type-level language, not the value-level one. More fundamentally, there's no way to tell GHC that a value-level computation corresponds to some type-level one.

This is where singletons come in [@eisenberg_dependently_2012]. A singleton is a type indexed by some type-level value, where there is only one value-level value for any given type-level value. In other words, there's only one inhabitant of every type. For the natural numbers, for instance, we could have this:

```{.haskell}
data Natty n where
    Zy :: Natty Z
    Sy :: Natty n -> Natty (S n)
```

Now, when we write a function on `Natty`{.haskell}, GHC knows that the values correspond to their types. And the `plusZeroNeutral`{.haskell} proof looks reasonably similar to the Idris version:

```{.haskell}
plusZeroNeutral :: Natty n -> n + Z :~: n
plusZeroNeutral Zy = Refl
plusZeroNeutral (Sy n) = case plusZeroNeutral n of
    Refl -> Refl
```

To generalize the singletons a little, we could probably use the [singletons](https://hackage.haskell.org/package/singletons) library, or we could roll our own:

```{.haskell}
data family The k :: k -> *

data instance The Nat n where
    Zy :: The Nat Z
    Sy :: The Nat n -> The Nat (S n)

plusZeroNeutral :: The Nat n -> n + Z :~: n
plusZeroNeutral Zy = Refl
plusZeroNeutral (Sy n) = case plusZeroNeutral n of
    Refl -> Refl
```

The `The`{.haskell} naming is kind of cute, I think. It makes the signature look *almost* like the Idris version (`the`{.idris} is a function from the Idris standard library).

### Proof Erasure and Totality

There's an issue with the above proof: it runs *every time* it is needed. Since the same value is coming out the other end each time (`Refl`{.haskell}), this seems wasteful.

In a language like Idris, this problem is avoided by noticing that you're only using the proof for its type information, and then erasing it at runtime. In Haskell, we can accomplish the same with a rule:

```{.haskell}
plusZeroNeutral :: The Nat n -> n + Z :~: n
plusZeroNeutral Zy = Refl
plusZeroNeutral (Sy n) = case plusZeroNeutral n of
  Refl -> Refl
{-# NOINLINE plusZeroNeutral #-}

{-# RULES
"plusZeroNeutral" forall x. plusZeroNeutral x 
  = unsafeCoerce (Refl :: 'Z :~: 'Z)
 #-}
```

This basically says "if this type-checks, then the proof must exist, and therefore the proof must be valid. So don't bother running it". Unfortunately, that's a *little bit* of a lie. It's pretty easy to write a proof which type-checks that *isn't* valid:

```{.haskell}
falseIsTrue :: False :~: True
falseIsTrue = falseIsTrue
```

We won't be able to perform computations which rely on this proof in Haskell, though: because the computation will never terminate, the proof will never provide an answer. Unless we use our manual proof-elision technique. The `RULES`{.haskell} pragma will happily replace it with the `unsafeCoerce`{.haskell} version, effectively introducing unsoundness into our proofs. The reason that this doesn't cause a problem for language like Idris is that Idris has a totality checker: you *can't* write the above definition (with the totality checker turned on) in Idris.

So what's the solution? Do we have to suffer through the slower proof code to maintain correctness? In reality, it's usually OK to assume termination. It's pretty easy to see that a proof like the above is total. It's worth bearing in mind, though, that until Haskell gets a totality checker ([likely never](https://typesandkinds.wordpress.com/2016/07/24/dependent-types-in-haskell-progress-report/), apparently) these proofs aren't "proper".

### Generating Singletons

One extra thing: while you're proving things in one area of your code, you might not have the relevant singleton handy. To generate them on-demand, you'll need a typeclass:

```{.haskell}
class KnownSing (x :: k) where
    sing :: The k x

instance KnownSing Z where
    sing = Zy

instance KnownSing n => KnownSing (S n) where
    sing = Sy sing
```

This kind of drives home the inefficiency of singleton-based proofs, and why it's important to erase them aggressively.

### Proofs Bundled with the Data Structure

One other way to solve these problems is to try find a data structure which runs the proof code anyway. As an example, consider a length-indexed list:

```{.haskell}
infixr 5 :-
data List n a where
    Nil :: List Z a
    (:-) :: a -> List n a -> List (S n) a
```

You might worry that concatenation of two lists requires some expensive proof code: surprisingly, though, the default implementation just works:

```{.haskell}
infixr 5 ++
(++) :: List n a -> List m a -> List (n + m) a
(++) Nil ys = ys
(++) (x :- xs) ys = x :- xs ++ ys
```

Why? Well, if you look back to the definition of `(+)`{.haskell}, it's almost exactly the same as the definition of `(++)`{.haskell}. In effect, we're using *lists* as the singleton for `Nat`{.haskell} here.

The question is, then: is there a data structure which performs these proofs automatically for functions like merge? So far, the answer looks like *kind of*. First though:

### Small Digression: Manipulating and Using the Length-Indexed List

The standard definition of `++`{.haskell} on normal lists can be cleaned up a little with `foldr`{.haskell}

```{.haskell}
(++) :: [a] -> [a] -> [a]
(++) = flip (foldr (:))
```

Can we get a similar definition for our length-indexed lists? Turns out we can, but the type of `foldr`{.haskell} needs to be a little different:

```{.haskell}
foldrList :: (forall x. a -> b x -> b (S x)) 
          -> b m -> List n a -> b (n + m)
foldrList f b Nil = b
foldrList f b (x :- xs) = f x (foldrList f b xs)

newtype Flip (f :: t -> u -> *) (a :: u) (b :: t) 
    = Flip { unFlip :: f b a }

foldrList1 :: (forall x. a -> b x c -> b (S x) c) 
           -> b m c -> List n a -> b (n + m) c
foldrList1 f b 
    = unFlip . foldrList (\e -> Flip . f e . unFlip) (Flip b)

infixr 5 ++
(++) :: List n a -> List m a -> List (n + m) a
(++) = flip (foldrList1 (:-))
```

So what's the point of this more complicated version? Well, if this were normal Haskell, we might get some foldr-fusion or something (in reality we would probably use [`augment`{.haskell}](http://hackage.haskell.org/package/base-4.9.1.0/docs/GHC-Exts.html#v:augment) if that were the purpose).

With this type-level business, though, there's a similar application: loop unrolling. Consider the natural-number type again. We can write a typeclass which will perform induction over them:

```{.haskell}
class KnownNat (n :: Nat)  where
    unrollRepeat :: Proxy n -> (a -> a) -> a -> a

instance KnownNat 'Z where
    unrollRepeat _ = const id
    {-# INLINE unrollRepeat #-}

instance KnownNat n =>
         KnownNat ('S n) where
    unrollRepeat (_ :: Proxy ('S n)) f x =
        f (unrollRepeat (Proxy :: Proxy n) f x)
    {-# INLINE unrollRepeat #-}
```

Because the recursion here isn't *really* recursion (we call a different `unrollRepeat`{.haskell} function in the "recursive" call), GHC will inline it. That means that the whole loop will be unrolled, at compile-time. We can do the same for foldr:

```{.haskell}
class HasFoldr (n :: Nat) where
    unrollFoldr 
        :: (forall x. a -> b x -> b (S x)) 
        -> b m 
        -> List n a 
        -> b (n + m)
  
instance HasFoldr Z where
    unrollFoldr _ b _ = b
    {-# INLINE unrollFoldr #-}

instance HasFoldr n => HasFoldr (S n) where
    unrollFoldr f b (x :- xs) = f x (unrollFoldr f b xs)
    {-# INLINE unrollFoldr #-}
```

This unrolling might be especially important if you wanted to, for instance, write a n-ary uncurry:

```{.haskell}
infixr 5 :-
data List (xs :: [*]) where
  Nil :: List '[]
  (:-) :: a -> List xs -> List (a ': xs)
    
class KnownList (xs :: [*])  where
    foldrT
        :: (forall y ys. y -> result ys -> result (y ': ys))
        -> (result '[])
        -> List xs
        -> result xs

instance KnownList ('[] :: [*]) where
    foldrT _ = const
    {-# INLINE foldrT #-}

instance KnownList xs =>
         KnownList (x ': xs) where
    foldrT f b (x :- xs) = f x (foldrT f b xs)
    {-# INLINE foldrT #-}

type family Func (xs :: [*]) (y :: *) where
  Func '[] y = y
  Func (x ': xs) y = x -> Func xs y    

newtype FunType y xs
  = FunType
  { runFun :: Func xs y -> y }

uncurry
    :: KnownList xs
    => Func xs y -> List xs -> y
uncurry f l =
    runFun
        (foldrT
             (\x (FunType g) ->
                   FunType (\h -> g (h x)))
             (FunType id)
             l)
        f
{-# INLINE uncurry #-}
```

I *think* that you can be guaranteed the above is inlined at compile-time, making it essentially equivalent to a handwritten `uncurry`{.haskell}.

### Binomial Heaps

Anyway, back to the size-indexed heaps. The reason that `(++)`{.haskell} worked so easily on lists is that a list can be thought of as the data-structure equivalent to Peano numbers. Another numeric-system-based data structure is the binomial heap, which is based on binary numbering [I'm going mainly off of the description from @hinze_functional_1999].

So, to work with binary numbers, let's get some preliminaries on the type-level out of the way:

```{.haskell}
data instance The Bool x where
    Falsy :: The Bool False
    Truey :: The Bool True

infixr 5 :-
data instance The [k] xs where
    Nily :: The [k] '[]
    (:-) :: The k x -> The [k] xs -> The [k] (x : xs)

instance KnownSing True where
    sing = Truey

instance KnownSing False where
    sing = Falsy

instance KnownSing '[] where
    sing = Nily

instance (KnownSing xs, KnownSing x) =>
         KnownSing (x : xs) where
    sing = sing :- sing
```

We'll represent a binary number as a list of Booleans:

```{.haskell}
type family Sum (x :: Bool) (y :: Bool) (cin :: Bool) :: Bool where
        Sum False False False = False
        Sum False False True  = True
        Sum False True  False = True
        Sum False True  True  = False
        Sum True  False False = True
        Sum True  False True  = True
        Sum True  True  False = False
        Sum True  True  True  = True

type family Carry (x :: Bool) (y :: Bool) (cin :: Bool)
     (xs :: [Bool]) (ys :: [Bool]) :: [Bool] where
        Carry False False False xs ys = Add False xs ys
        Carry False False True  xs ys = Add False xs ys
        Carry False True  False xs ys = Add False xs ys
        Carry False True  True  xs ys = Add True  xs ys
        Carry True  False False xs ys = Add False xs ys
        Carry True  False True  xs ys = Add True  xs ys
        Carry True  True  False xs ys = Add True  xs ys
        Carry True  True  True  xs ys = Add True  xs ys

type family Add (cin :: Bool) (xs :: [Bool]) (ys :: [Bool]) ::
     [Bool] where
        Add c (x : xs) (y : ys) = Sum x y c : Carry x y c xs ys
        Add False '[] ys = ys
        Add False xs '[] = xs
        Add True  '[] ys = CarryOne ys
        Add True  xs '[] = CarryOne xs

type family CarryOne (xs :: [Bool]) :: [Bool] where
        CarryOne '[] = True : '[]
        CarryOne (False : xs) = True : xs
        CarryOne (True  : xs) = False : CarryOne xs
```

The odd definition of `Carry`{.haskell} is to avoid `-XUndecidableInstances`{.haskell}: if we had written, instead:

```{.haskell}
type family Carry (x :: Bool) (y :: Bool) (cin :: Bool) :: Bool where
        Carry False False False = False
        Carry False False True  = False
        Carry False True  False = False
        Carry False True  True  = True
        Carry True  False False = False
        Carry True  False True  = True
        Carry True  True  False = True
        Carry True  True  True  = True

type family Add (cin :: Bool) (xs :: [Bool]) (ys :: [Bool]) ::
     [Bool] where
        Add c (x : xs) (y : ys) = Sum x y c : Add (Carry x y c) xs ys
        Add False '[] ys = ys
        Add False xs '[] = xs
        Add True  '[] ys = CarryOne ys
        Add True  xs '[] = CarryOne xs
```

We would have been warned about nested type-family application.

The already-existing 

* dependent if-then-else
* [@wasserman_playing_2010, @okasaki_fast_1999].
* Manual proof on binomial heap
* Parity and "doubly-dependent" (types indexed by indexed types) - http://stackoverflow.com/a/13241158/4892417
* SMT solvers etc - Diatchki paper, there and back again paper (and video). Eventual normalizing solver [@diatchki_improving_2015, @danvy_there_2005] https://www.youtube.com/watch?v=u_OsUlwkmBQ
* Machine-integer-backed singletons (leftist heap)
* Generalizing Sort to Parts.
* Other uses for size-indexed heaps? Primes? 
