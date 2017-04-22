---
title: Verifying Data Structures in Haskell
bibliography: Data Structures.bib
---

```{.haskell .literate .hidden_source}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}


module VerifiedDataStructures where

import Data.Kind
import Data.Type.Equality
import Unsafe.Coerce
```

A while ago I read [this](https://www.reddit.com/r/haskell/comments/63a4ea/fast_total_sorting_of_arbitrary_traversable/) post on reddit (by David Feuer), about sorting traversables, and I was inspired to write some pseudo-dependently-typed Haskell. The post (and subsequent [library](https://github.com/treeowl/sort-traversable)) detailed how to use size-indexed heaps to perform fast, total sorting on any traversable. I ended up with a [library](https://github.com/oisdk/type-indexed-heaps) which has both verified and unverified versions of heaps, in order to compare the difficulty of implementations (as well as benchmarks, tests, and all that good stuff).

### Type-Level Numbers in Haskell

The normal representation of type-level natural numbers is [Peano](https://wiki.haskell.org/Peano_numbers) numbers:

```{.haskell .literate}
data Nat = Z | S Nat
```

The terseness is pretty necessary here, unfortunately: arithmetic becomes unreadable otherwise. Regardless, `Z`{.haskell} stands for zero, and `S`{.haskell} for successor.

With the `-XDataKinds`{.haskell} extension, the above is automatically promoted to the type-level, as well as the value-level, so we can write type-level functions (type families) on the `Nat`{.haskell} type:

```{.haskell .literate}
type family (+) (n :: Nat) (m :: Nat) :: Nat where
  Z + m = m
  S n + m = S (n + m)
```

The number of extensions turned on here is going to quickly get out of hand, so rather than enumerate each one as they come up, I'll just direct you to a repository with these examples at the end (quick aside: `-XUndecidableInstances`{.haskell} is *not* used at any point here, but more on that later). One pragma that's worth mentioning is:

```{.haskell .literate}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}
```

Type-level code with a load of ticks can look pretty ugly, and the warnings aren't very helpful if you're doing a lot of type-level stuff. Watch out for `[]`{.haskell}, though: it always needs to be ticked to work properly.

### Using the Type-Level Numbers with a Pairing Heap

In the original post, a pairing heap [@fredman_pairing_1986] was used, for its simplicity and performance. The implementation looked like this:

```{.haskell .literate}
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

```{.haskell .literate}
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

```{.haskell .literate}
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

```{.haskell .literate}
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
        -> result '[]
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

newtype FunType y xs = FunType
    { runFun :: Func xs y -> y
    }

uncurry
    :: KnownList xs
    => Func xs y -> List xs -> y
uncurry f l =
    runFun
        (foldrT
             (c (\x g h -> g (h x)))
             (FunType id)
             l)
        f
  where
    c :: (a -> ((Func xs y -> y) -> (Func zs z -> z)))
      -> (a -> (FunType y xs -> FunType z zs))
    c = coerce
    {-# INLINE c #-}
{-# INLINE uncurry #-}
```

I *think* that you can be guaranteed the above is inlined at compile-time, making it essentially equivalent to a handwritten `uncurry`{.haskell}.

### Binomial Heaps

Anyway, back to the size-indexed heaps. The reason that `(++)`{.haskell} worked so easily on lists is that a list can be thought of as the data-structure equivalent to Peano numbers. Another numeric-system-based data structure is the binomial heap, which is based on binary numbering [I'm going mainly off of the description from @hinze_functional_1999].

So, to work with binary numbers, let's get some preliminaries on the type-level out of the way:

```{.haskell .literate}
data instance The Bool x where
    Falsy :: The Bool False
    Truey :: The Bool True

data instance The [k] xs where
    Nily :: The [k] '[]
    Cony :: The k x -> The [k] xs -> The [k] (x : xs)

instance KnownSing True where
    sing = Truey

instance KnownSing False where
    sing = Falsy

instance KnownSing '[] where
    sing = Nily

instance (KnownSing xs, KnownSing x) =>
         KnownSing (x : xs) where
    sing = Cony sing sing
```

We'll represent a binary number as a list of Booleans:

```{.haskell .literate}
type family Sum (x :: Bool) (y :: Bool) (cin :: Bool) :: Bool where
        Sum False False False = False
        Sum False False True  = True
        Sum False True  False = True
        Sum False True  True  = False
        Sum True  False False = True
        Sum True  False True  = False
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

Now we can base the merge function very closely on these type families. First, though, we'll have to implement the heap.

### Almost-Verified Data Structures

There are different potential properties you can verify in a data structure. In this post, I'll only be really looking at structural invariants. I won't be verifying the [heap property](https://www.cs.cmu.edu/~adamchik/15-121/lectures/Binary%20Heaps/heaps.html), for instance.

For size-indexed heaps, an awful lot of information about the structure is statically known. However, a lot of properties can be ensured with far less information. Here's a signature for "perfect leaf tree":

```{.haskell .literate}
data BalTree a = Leaf a | Node (BalTree (a,a))
```

With that signature, it's *impossible* to create a tree with more elements in its left branch than its right. However, the size of that tree is not statically known. You can use a similar trick to implement [matrices which must be square](https://github.com/oisdk/Square) [from @okasaki_fast_1999] (this is *not* the rather ugly `type Matrix n a = List n (List n a)`{.haskell}). These sorts of tricks are explored in general in @hinze_manufacturing_2001.

For binomial heaps, the approach I'll be using is similar to @wasserman_playing_2010, except with a slightly more modern implementation: where Wasserman's version used types like this for the numbering:

```{.haskell}
data Zero a = Zero
data Succ rk a = BinomTree rk a :< rk a
data BinomTree rk a = BinomTree a (rk a)
```

We can reuse the type-level Peano numbers with a GADT.

### A Fully-Structurally-Verified Binomial Heap

```{.haskell .literate}
infixr 5 :-
data Binomial xs rk a where
       Nil :: Binomial '[] n a
       Skip :: Binomial xs (S rk) a -> Binomial (False : xs) rk a
       (:-) :: Tree rk a 
            -> Binomial xs (S rk) a 
            -> Binomial (True : xs) rk a

data Tree rk a = Root a (Node rk a)

infixr 5 :<
data Node n a where
       NilN :: Node Z a
       (:<) :: Tree n a -> Node n a -> Node (S n) a
```

The definition of `Tree`{.haskell} here ensures that any tree of rank $n$ has $2^n$ elements. The binomial heap, then, is a list of trees, in ascending order of size, with a `True`{.haskell} at every point in its type-level list where a tree is present, and a `False`{.haskell} wherever one is absent. In other words, the type-level list is a binary encoding of the number of elements it contains.

And here are the merge functions:

```{.haskell .literate}
mergeTree :: Ord a => Tree rk a -> Tree rk a -> Tree (S rk) a
mergeTree xr@(Root x xs) yr@(Root y ys)
  | x <= y    = Root x (yr :< xs)
  | otherwise = Root y (xr :< ys)

merge 
    :: Ord a 
    => Binomial xs z a 
    -> Binomial ys z a 
    -> Binomial (Add False xs ys) z a
merge Nil ys              = ys
merge xs Nil              = xs
merge (Skip xs) (Skip ys) = Skip (merge xs ys)
merge (Skip xs) (y :- ys) = y :- merge xs ys
merge (x :- xs) (Skip ys) = x :- merge xs ys
merge (x :- xs) (y :- ys) = Skip (mergeCarry (mergeTree x y) xs ys)

mergeCarry
    :: Ord a
    => Tree rk a 
    -> Binomial xs rk a 
    -> Binomial ys rk a 
    -> Binomial (Add True xs ys) rk a
mergeCarry t Nil ys              = carryOne t ys
mergeCarry t xs Nil              = carryOne t xs
mergeCarry t (Skip xs) (Skip ys) = t :- merge xs ys
mergeCarry t (Skip xs) (y :- ys) = Skip (mergeCarry (mergeTree t y) xs ys)
mergeCarry t (x :- xs) (Skip ys) = Skip (mergeCarry (mergeTree t x) xs ys)
mergeCarry t (x :- xs) (y :- ys) = t :- mergeCarry (mergeTree x y) xs ys

carryOne 
    :: Ord a 
    => Tree rk a -> Binomial xs rk a -> Binomial (CarryOne xs) rk a
carryOne t Nil       = t :- Nil
carryOne t (Skip xs) = t :- xs
carryOne t (x :- xs) = Skip (carryOne (mergeTree t x) xs)
```

You'll notice that no proofs are needed: that's because the merge function itself is the same as the type family, like the way `++`{.haskell} for lists was the same as the `+`{.haskell} type family.

Of course, this structure is only verified insofar as you believe the type families. If there's a mistake in one of them, and a mistake in the merge function which mirrors the same mistake, the that won't be caught. However, we can write some proofs of the properties of the type families that we would expect:

```{.haskell .literate}
addCommutes
  :: The [Bool] xs
  -> The [Bool] ys
  -> Add False xs ys :~: Add False ys xs
addCommutes Nily _ = Refl
addCommutes _ Nily = Refl
addCommutes (Cony Falsy xs) (Cony Falsy ys) =
    gcastWith (addCommutes xs ys) Refl
addCommutes (Cony Truey xs) (Cony Falsy ys) =
    gcastWith (addCommutes xs ys) Refl
addCommutes (Cony Falsy xs) (Cony Truey ys) =
    gcastWith (addCommutes xs ys) Refl
addCommutes (Cony Truey xs) (Cony Truey ys) =
    gcastWith (addCommutesCarry xs ys) Refl

addCommutesCarry
  :: The [Bool] xs
  -> The [Bool] ys
  -> Add True xs ys :~: Add True ys xs
addCommutesCarry Nily _ = Refl
addCommutesCarry _ Nily = Refl
addCommutesCarry (Cony Falsy xs) (Cony Falsy ys) =
    gcastWith (addCommutes xs ys) Refl
addCommutesCarry (Cony Truey xs) (Cony Falsy ys) =
    gcastWith (addCommutesCarry xs ys) Refl
addCommutesCarry (Cony Falsy xs) (Cony Truey ys) =
    gcastWith (addCommutesCarry xs ys) Refl
addCommutesCarry (Cony Truey xs) (Cony Truey ys) =
    gcastWith (addCommutesCarry xs ys) Refl
```

Unfortunately, though, this method *does* require proofs (ugly proofs) for the delete-min operation. One particularly nasty aspect is that you need to change the original signature of the heap: our version above doesn't guarantee that the binary representation is truncated. Since it's stored least-significant-bit first, there could be trailing zeroes without changing the numerical value. From what I've tried with the delete-min operation, it looks like I need to show that there *aren't* any trailing zeroes, which would require a change to the type.

### Doubly-Dependent Types

The troublemaker for the binomial heap is the *decrement* type family. As shown above, it's reasonably easy to show commutativity on the addition of binary numbers, but it turns out to be quite a bit more difficult to prove some other properties, especially surrounding subtraction.

Since some of these properties are much easier to verify on the type-level Peano numbers, one approach might be to convert back and forth between Peano numbers and binary, and use the proofs on Peano numbers instead.

```{.haskell}
type family BintoNat (xs :: [Bool]) :: Nat where
        BintoNat '[] = Z
        BintoNat (False : xs) = BintoNat xs + BintoNat xs
        BintoNat (True : xs) = S (BintoNat xs + BintoNat xs)
```

First problem: this requires `-XUndecidableInstances`{.haskell}. I'd *really* rather not have that turned on, to be honest. In Idris (and Agda), you can *prove* decidability using [a number of different methods](https://www.idris-lang.org/docs/0.12/contrib_doc/docs/Control.WellFounded.html), but this isn't available in Haskell yet.

Regardless, we can push on.

To go in the other direction, we can take the example from the Idris tutorial:

```{.haskell}
data Parity (n :: Nat) where
    Even :: The Nat n -> Parity (n + n)
    Odd  :: The Nat n -> Parity (S (n + n))

parity :: The Nat n -> Parity n
parity Zy = Even Zy
parity (Sy Zy) = Odd Zy
parity (Sy (Sy n)) = case parity n of
  Even m -> gcastWith (plusSuccDistrib m m) (Even (Sy m))
  Odd  m -> gcastWith (plusSuccDistrib m m) (Odd (Sy m))

plusSuccDistrib :: The Nat n -> proxy m -> n + S m :~: S (n + m)
plusSuccDistrib Zy _ = Refl
plusSuccDistrib (Sy n) p = gcastWith (plusSuccDistrib n p) Refl
```

The `parity`{.haskell} function can help us later convert to binary. There's an issue, though: it's defined on the value-level, not type-level. in fact, I don't think you *can* promote it to the type level, as there's no type-level `gcastWith`{.haskell}.

This idea of doing dependently-typed stuff on the type-level *started* to be possible with `-XTypeInType`{.haskell}. For instance, we could have defined our binary type as:

```{.haskell}
data Binary :: Nat -> Type where
    O :: Binary n -> Binary (n + n)
    I :: Binary n -> Binary (S (n + n))
    E :: Binary Z
```

And then the binomial heap as:

```{.haskell}
data Binomial (xs :: Binary n) (rk :: Nat) (a :: Type) where
       Nil :: Binomial E n a
       Skip :: Binomial xs (S rk) a -> Binomial (O xs) rk a
       (:-) :: Tree rk a 
            -> Binomial xs (S rk) a 
            -> Binomial (I xs) rk a
```

What we're doing here is indexing a type *by an indexed type*. [This wasn't possible in Haskell a few years ago](http://stackoverflow.com/a/13241158/4892417).

### Using a Typechecker Plugin

It's pretty clear that this approach gets tedious almost immediately. What's more, if we want the proofs to be erased, we introduce potential for errors.

The solution? Beef up GHC's typechecker with a plugin. I first came across this approach in [Kenneth Foner's talk at Compose](https://www.youtube.com/watch?v=u_OsUlwkmBQ). He used a plugin that called out to the [Z3 theorem prover](https://github.com/Z3Prover/z3) [from @diatchki_improving_2015]; I'll use a [simpler plugin](https://hackage.haskell.org/package/ghc-typelits-natnormalise) which just normalizes type-literals. Each typechecker plugin is called when GHC can't unify two types: other than that, there's no real change to the code. Another benefit is that we get to use type-level literals, rather then the noisy-looking type-level Peano numbers.

It works surprisingly well. The code is almost unchanged from the non-indexed version:

```{.haskell}
data Tree n a = Root a (Node n a)

data Node :: Nat -> * -> * where
        NilN :: Node 0 a
        (:<) :: Tree n a
             -> Node n a
             -> Node (1 + n) a

mergeTree :: Ord a => Tree n a -> Tree n a -> Tree (1 + n) a
mergeTree xr@(Root x xs) yr@(Root y ys)
  | x <= y    = Root x (yr :< xs)
  | otherwise = Root y (xr :< ys)

infixr 5 :-
data Binomial :: Nat -> Nat -> * -> * where
        Nil  :: Binomial n 0 a
        (:-) :: Tree z a
             -> Binomial (1 + z) xs a
             -> Binomial z (1 + xs + xs) a
        Skip :: Binomial (1 + z) (1 + xs) a
             -> Binomial z (2 + xs + xs) a

merge
    :: Ord a
    => Binomial z xs a -> Binomial z ys a -> Binomial z (xs + ys) a
merge Nil ys              = ys
merge xs Nil              = xs
merge (Skip xs) (Skip ys) = Skip (merge xs ys)
merge (Skip xs) (y :- ys) = y :- merge xs ys
merge (x :- xs) (Skip ys) = x :- merge xs ys
merge (x :- xs) (y :- ys) = Skip (mergeCarry (mergeTree x y) xs ys)

mergeCarry
    :: Ord a
    => Tree z a
    -> Binomial z xs a
    -> Binomial z ys a
    -> Binomial z (1 + xs + ys) a
mergeCarry t Nil ys              = carryOne t ys
mergeCarry t xs Nil              = carryOne t xs
mergeCarry t (Skip xs) (Skip ys) = t :- merge xs ys
mergeCarry t (Skip xs) (y :- ys) = Skip (mergeCarry (mergeTree t y) xs ys)
mergeCarry t (x :- xs) (Skip ys) = Skip (mergeCarry (mergeTree t x) xs ys)
mergeCarry t (x :- xs) (y :- ys) = t :- mergeCarry (mergeTree x y) xs ys

carryOne 
  :: Ord a 
  => Tree z a 
  -> Binomial z xs a 
  -> Binomial z (1 + xs) a
carryOne t Nil       = t :- Nil
carryOne t (Skip xs) = t :- xs
carryOne t (x :- xs) = Skip (carryOne (mergeTree t x) xs)
```

On top of that, it's very easy to define delete-min:

```{.haskell}
data Zipper a n rk = Zipper !a (Node rk a) (Binomial rk n a)

skip :: Binomial (1 + z) xs a -> Binomial z (xs + xs) a
skip x = case x of
  Nil    -> Nil
  Skip _ -> Skip x
  _ :- _ -> Skip x

data MinViewZipper a n rk where
    Infty :: MinViewZipper a 0 rk
    Min :: Zipper a n rk -> MinViewZipper a (n+1) rk

slideLeft :: Zipper a n (1 + rk) -> Zipper a (1 + n + n) rk
slideLeft (Zipper m (t :< ts) hs)
  = Zipper m ts (t :- hs)

pushLeft 
  :: Ord a 
  => Tree rk a 
  -> Zipper a n (1 + rk) 
  -> Zipper a (2 + n + n) rk
pushLeft c (Zipper m (t :< ts) hs)
  = Zipper m ts (Skip (carryOne (mergeTree c t) hs))

minViewZip :: Ord a => Binomial rk (1 + n) a -> Zipper a n rk
minViewZip (Skip xs) = slideLeft (minViewZip xs)
minViewZip (t@(Root x ts) :- f) = case minViewZipMay f of
  Min ex@(Zipper minKey _ _) | minKey < x -> pushLeft t ex
  _                          -> Zipper x ts (skip f)

minViewZipMay :: Ord a => Binomial rk n a -> MinViewZipper a n rk
minViewZipMay (Skip xs) = Min (slideLeft (minViewZip xs))
minViewZipMay Nil = Infty
minViewZipMay (t@(Root x ts) :- f) = Min $ case minViewZipMay f of
  Min ex@(Zipper minKey _ _) | minKey < x -> pushLeft t ex
  _                          -> Zipper x ts (skip f)

minView :: Ord a => Binomial Z (1 + n) a -> (a, Binomial Z n a)
minView xs = case minViewZip xs of
      Zipper x _ ys -> (x, ys)
```

Similarly, compare the version of the pairing heap with the plugin:

```{.haskell}
data Heap n a where
  E :: Heap 0 a
  T :: a -> HVec n a -> Heap (1 + n) a

data HVec n a where
  HNil :: HVec 0 a
  HCons :: Heap m a -> HVec n a -> HVec (m + n) a

insert :: Ord a => a -> Heap n a -> Heap (1 + n) a
insert x xs = merge (T x HNil) xs

merge :: Ord a => Heap m a -> Heap n a -> Heap (m + n) a
merge E ys = ys
merge xs E = xs
merge h1@(T x xs) h2@(T y ys)
  | x <= y = T x (HCons h2 xs)
  | otherwise = T y (HCons h1 ys)

minView :: Ord a => Heap (1 + n) a -> (a, Heap n a)
minView (T x hs) = (x, mergePairs hs)

mergePairs :: Ord a => HVec n a -> Heap n a
mergePairs HNil = E
mergePairs (HCons h HNil) = h
mergePairs (HCons h1 (HCons h2 hs)) =
    merge (merge h1 h2) (mergePairs hs)
```

To the version without the plugin:


```{.haskell}
data Heap n a where
  E :: Heap Z a
  T :: a -> HVec n a -> Heap (S n) a

data HVec n a where
  HNil :: HVec Z a
  HCons :: Heap m a -> HVec n a -> HVec (m + n) a

class Sized h where
  size :: h n a -> The Nat n

instance Sized Heap where
  size E = Zy
  size (T _ xs) = Sy (size xs)

plus :: The Nat n -> The Nat m -> The Nat (n + m)
plus Zy m = m
plus (Sy n) m = Sy (plus n m)

instance Sized HVec where
  size HNil = Zy
  size (HCons h hs) = size h `plus` size hs

insert :: Ord a => a -> Heap n a -> Heap (S n) a
insert x xs = merge (T x HNil) xs

merge :: Ord a => Heap m a -> Heap n a -> Heap (m + n) a
merge E ys = ys
merge xs E = case plusZero (size xs) of Refl -> xs
merge h1@(T x xs) h2@(T y ys)
  | x <= y = case plusCommutative (size h2) (size xs) of
                    Refl -> T x (HCons h2 xs)
  | otherwise = case plusSuccDistrib (size xs) (size ys) of
                    Refl -> T y (HCons h1 ys)

minView :: Ord a => Heap (S n) a -> (a, Heap n a)
minView (T x hs) = (x, mergePairs hs)

mergePairs :: Ord a => HVec n a -> Heap n a
mergePairs HNil = E
mergePairs (HCons h HNil) = case plusZero (size h) of Refl -> h
mergePairs (HCons h1 (HCons h2 hs)) =
  case plusAssoc (size h1) (size h2) (size hs) of
    Refl -> merge (merge h1 h2) (mergePairs hs)
```

### Leftist Heaps




---

* dependent if-then-else
* Machine-integer-backed singletons (leftist heap)
* Generalizing Sort to Parts.
* Other uses for size-indexed heaps? Primes? 

---
