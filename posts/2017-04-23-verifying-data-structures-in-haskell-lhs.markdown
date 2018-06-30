---
title: Verifying Data Structures in Haskell
bibliography: Data Structures.bib
tags: Haskell, Dependent Types, Data Structures
---

```{.haskell .literate .hidden_source}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RebindableSyntax #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module VerifiedDataStructures where

import Data.Kind hiding (type (*))
import Data.Type.Equality
import Unsafe.Coerce
import GHC.TypeLits hiding (type (<=))
import Data.Proxy
import Data.Coerce
import Prelude
```

A while ago I read [this](https://www.reddit.com/r/haskell/comments/63a4ea/fast_total_sorting_of_arbitrary_traversable/) post on reddit (by David Feuer), about sorting traversables (which was a follow-up on [this](http://elvishjerricco.github.io/2017/03/23/applicative-sorting.html) post by Will Fancher), and I was inspired to write some pseudo-dependently-typed Haskell. The post (and subsequent [library](https://github.com/treeowl/sort-traversable)) detailed how to use size-indexed heaps to perform fast, total sorting on any traversable. I ended up with a [library](https://github.com/oisdk/type-indexed-queues) which has five size-indexed heaps (Braun, pairing, binomial, skew, and leftist), each verified for structural correctness. I also included the non-indexed implementations of each for comparison (as well as benchmarks, tests, and all that good stuff).

The purpose of this post is to go through some of the tricks I used and problems I encountered writing a lot of type-level code in modern Haskell.

### Type-Level Numbers in Haskell

In order to index things by their size, we'll need a type-level representation of size. We'll use [Peano](https://wiki.haskell.org/Peano_numbers) numbers for now:

```{.haskell .literate}
data Peano = Z | S Peano
```

`Z`{.haskell} stands for zero, and `S`{.haskell} for successor. The terseness is pretty necessary here, unfortunately: arithmetic becomes unreadable otherwise. The simplicity of this definition is useful for proofs and manipulation; however any runtime representation of these numbers is going to be woefully slow.

With the `DataKinds`{.haskell} extension, the above is automatically promoted to the type-level, so we can write type-level functions (type families) on the `Peano`{.haskell} type:

```{.haskell .literate}
type family Plus (n :: Peano) (m :: Peano) :: Peano where
        Plus Z m = m
        Plus (S n) m = S (Plus n m)
```

Here the `TypeFamilies`{.haskell} extension is needed. I'll try and mention every extension I'm using as we go, but I might forget a few, so check the repository for all of the examples (quick aside: I *did* manage to avoid using `UndecidableInstances`{.haskell}, but more on that later). One pragma that's worth mentioning is:

```{.haskell .literate}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}
```

This suppresses warnings on the definition of `Plus`{.haskell} above. Without it, GHC would want us to write:

```{.haskell}
type family Plus (n :: Peano) (m :: Peano) :: Peano where
        Plus 'Z m = m
        Plus ('S n) m = 'S (Plus n m)
```

I think that looks pretty ugly, and it can get much worse with more involved arithmetic. The only thing I have found the warnings useful for is `[]`{.haskell}: the type-level empty list gives an error in its unticked form.

### Using the Type-Level Numbers with a Pairing Heap

In the original post, a pairing heap [@fredman_pairing_1986] was used, for its simplicity and performance. The implementation looked like this:

```{.haskell .literate}
data Heap n a where
  E :: Heap Z a
  T :: a -> HVec n a -> Heap (S n) a

data HVec n a where
  HNil :: HVec Z a
  HCons :: Heap m a -> HVec n a -> HVec (Plus m n) a
```

You immediately run into trouble when you try to define merge:

```{.haskell}
merge :: Ord a => Heap m a -> Heap n a -> Heap (Plus m n) a
merge E ys = ys
merge xs E = xs
merge h1@(T x xs) h2@(T y ys)
  | x <= y = T x (HCons h2 xs)
  | otherwise = T y (HCons h1 ys)
```

Three errors show up here, but we'll look at the first one: 

> `Could not deduce (m ~ (Plus m Z))`
    
GHC doesn't know that $x = x + 0$. Somehow, we'll have to *prove* that it does.

### Singletons

In a language with true dependent types, proving the proposition above is as simple as:

```{.idris}
plusZeroNeutral : (n : Nat) -> n + 0 = n
plusZeroNeutral Z = Refl
plusZeroNeutral (S k) = cong (plusZeroNeutral k)
```

(this example is in Idris)

In Haskell, on the other hand, we can't do the same: functions on the value-level `Peano`{.haskell} have no relationship with functions on the type-level `Peano`{.haskell}. There's no way to automatically link or promote one to the other.

This is where singletons come in [@eisenberg_dependently_2012]. A singleton is a datatype which mirrors a type-level value exactly, except that it has a type parameter which matches the equivalent value on the type-level. In this way, we can write functions on the value-level which are linked to the type-level. Here's a potential singleton for `Peano`{.haskell}:

```{.haskell}
data Natty n where
    Zy :: Natty Z
    Sy :: Natty n -> Natty (S n)
```

(we need `GADTs`{.haskell} for this example)

Now, when we pattern-match on `Natty`{.haskell}, we get a proof of whatever its type parameter was. Here's a trivial example:

```{.haskell}
isZero :: Natty n -> Maybe (n :~: Z)
isZero Zy = Just Refl
isZero (Sy _) = Nothing
```

When we match on `Zy`{.haskell}, the *only value* which `n`{.haskell} could have been is `Z`{.haskell}, because the only way to construct `Zy`{.haskell} is if the type parameter is `Z`{.haskell}.

Using this technique, the `plusZeroNeutral`{.haskell} proof looks reasonably similar to the Idris version:

```{.haskell}
plusZeroNeutral :: Natty n -> Plus n Z :~: n
plusZeroNeutral Zy = Refl
plusZeroNeutral (Sy n) = case plusZeroNeutral n of
    Refl -> Refl
```

To generalize the singletons a little, we could probably use the [singletons](https://hackage.haskell.org/package/singletons) library, or we could roll our own:

```{.haskell .literate}
data family The k :: k -> Type

data instance The Peano n where
    Zy :: The Peano Z
    Sy :: The Peano n -> The Peano (S n)

plusZeroNeutral :: The Peano n -> Plus n Z :~: n
plusZeroNeutral Zy = Refl
plusZeroNeutral (Sy n) = case plusZeroNeutral n of
    Refl -> Refl
```

The `The`{.haskell} naming is kind of cute, I think. It makes the signature look *almost* like the Idris version (`the`{.idris} is a function from the Idris standard library). The `The`{.haskell} type family requires the `TypeInType`{.haskell} extension, which I'll talk a little more about later.

### Proof Erasure and Totality

There's an issue with these kinds of proofs: the proof code runs *every time* it is needed. Since the same value is coming out the other end each time (`Refl`{.haskell}), this seems wasteful.

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

We won't be able to perform computations which rely on this proof in Haskell, though: because the computation will never terminate, the proof will never provide an answer. This means that, while the proof isn't valid, it *is* type safe. That is, of course, unless we use our manual proof-erasure technique. The `RULES`{.haskell} pragma will happily replace it with the `unsafeCoerce`{.haskell} version, effectively introducing unsoundness into our proofs. The reason that this doesn't cause a problem for language like Idris is that Idris has a totality checker: you *can't* write the above definition (with the totality checker turned on) in Idris.

So what's the solution? Do we have to suffer through the slower proof code to maintain correctness? In reality, it's usually OK to assume termination. It's pretty easy to see that a proof like `plusZeroNeutral`{.haskell} is total. It's worth bearing in mind, though, that until Haskell gets a totality checker ([likely never](https://typesandkinds.wordpress.com/2016/07/24/dependent-types-in-haskell-progress-report/), apparently) these proofs aren't "proper".

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

You might worry that concatenation of two lists requires some expensive proof code, like `merge`{.haskell} for the pairing heap. Maybe surprisingly, the default implementation just works:

```{.haskell}
infixr 5 ++
(++) :: List n a -> List m a -> List (Plus n m) a
(++) Nil ys = ys
(++) (x :- xs) ys = x :- xs ++ ys
```

Why? Well, if you look back to the definition of `Plus`{.haskell}, it's almost exactly the same as the definition of `(++)`{.haskell}. In effect, we're using *lists* as the singleton for `Peano`{.haskell} here.

The question is, then: is there a heap which performs these proofs automatically for functions like merge? As far as I can tell: *almost*. First though:

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

newtype Flip (f :: t -> u -> Type) (a :: u) (b :: t) 
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
class KnownPeano (n :: Peano)  where
    unrollRepeat :: Proxy n -> (a -> a) -> a -> a

instance KnownPeano Z where
    unrollRepeat _ = const id
    {-# INLINE unrollRepeat #-}

instance KnownPeano n =>
         KnownPeano (S n) where
    unrollRepeat (_ :: Proxy (S n)) f x =
        f (unrollRepeat (Proxy :: Proxy n) f x)
    {-# INLINE unrollRepeat #-}
```

Because the recursion here calls a different `unrollRepeat`{.haskell} function in the "recursive" call, we get around the [usual hurdle](http://stackoverflow.com/questions/42179783/is-there-any-way-to-inline-a-recursive-function) of not being able to inline recursive calls. That means that the whole loop will be unrolled, at compile-time. We can do the same for foldr:

```{.haskell}
class HasFoldr (n :: Peano) where
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

I can't think of many uses for this technique, but one that comes to mind is an n-ary uncurry (like Lisp's [apply](https://en.wikipedia.org/wiki/Apply#Common_Lisp_and_Scheme)):

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

The odd definition of `Carry`{.haskell} is to avoid `UndecidableInstances`{.haskell}: if we had written, instead:

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

There are different potential properties you can verify in a data structure. In the sort-traversable post, the property of interest was that the number of elements in the structure would stay the same after adding and removing some number $n$ of elements. For this post, we'll also verify structural invariants. I won't, however, verify the [heap property](https://www.cs.cmu.edu/~adamchik/15-121/lectures/Binary%20Heaps/heaps.html). Maybe in a later post.


When indexing a data structure by its size, you encode an awful lot of information into the type signature: the type becomes very *specific* to the structure in question. It is possible, though, to encode a fair few structural invariants *without* getting so specific. Here's a signature for "perfect leaf tree":

```{.haskell}
data BalTree a = Leaf a | Node (BalTree (a,a))
```

With that signature, it's *impossible* to create a tree with more elements in its left branch than its right; the size of the tree, however, remains unspecified. You can use a similar trick to implement [matrices which must be square](https://github.com/oisdk/Square) [from @okasaki_fast_1999]: the usual trick (`type Matrix n a = List n (List n a)`{.haskell}) is too specific, providing size information at compile-time. If you're interested in this approach, there are several more examples in @hinze_manufacturing_2001.

It is possible to go from the size-indexed version back to the non-indexed version, with an existential (`RankNTypes`{.haskell} for this example):

```{.haskell .literate}
data ErasedSize f a = forall (n :: Peano). ErasedSize
    { runErasedSize :: f n a
    }
```

This will let you prove invariants in your implementation using an index, while keeping the user-facing type signature general and non-indexed.

### A Fully-Structurally-Verified Binomial Heap

@wasserman_playing_2010, was able to encode all of the structural invariants of the binomial heap *without* indexing by its size (well, all invariants except truncation, which turned out to be important a little later). I'll be using a similar approach, except I'll leverage some of the newer bells and whistles in GHC. Where Wasserman's version used types like this for the numbering:

```{.haskell}
data Zero a = Zero
data Succ rk a = BinomTree rk a :< rk a
data BinomTree rk a = BinomTree a (rk a)
```

We can reuse the type-level Peano numbers with a GADT:


```{.haskell}
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

```{.haskell}
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

You'll notice that no proofs are needed: that's because the merge function itself is the same as the type family, like the way `++`{.haskell} for lists was the same as the `Plus`{.haskell} type family.

Of course, this structure is only verified insofar as you believe the type families. It does provide a degree of double-entry, though: any mistake in the type family will have to be mirrored in the merge function to type-check. On top of that, we can write some proofs of properties we might expect:

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

Unfortunately, though, this method *does* require proofs (ugly proofs) for the delete-min operation. One of the issues is truncation: since the binary digits are stored least-significant-bit first, the same number can be represented with any number of trailing zeroes. This kept causing problems for me when it came to subtraction, and adding the requirement of no trailing zeroes (truncation) to the constructors for the heap was a pain, requiring extra proofs on merge to show that it preserves truncation.

### Doubly-Dependent Types

Since some of these properties are much easier to verify on the type-level Peano numbers, one approach might be to convert back and forth between Peano numbers and binary, and use the proofs on Peano numbers instead.

```{.haskell}
type family BintoPeano (xs :: [Bool]) :: Peano where
        BintoPeano '[] = Z
        BintoPeano (False : xs) = BintoPeano xs + BintoPeano xs
        BintoPeano (True : xs) = S (BintoPeano xs + BintoPeano xs)
```

First problem: this requires `UndecidableInstances`{.haskell}. I'd *really* rather not have that turned on, to be honest. In Idris (and Agda), you can *prove* decidability using [a number of different methods](https://www.idris-lang.org/docs/0.12/contrib_doc/docs/Control.WellFounded.html), but this isn't available in Haskell yet.

Regardless, we can push on.

To go in the other direction, we'll need to calculate the parity of natural numbers. Taken from [the Idris tutorial](http://docs.idris-lang.org/en/latest/tutorial/theorems.html#theorems-in-practice):

```{.haskell}
data Parity (n :: Peano) where
    Even :: The Peano n -> Parity (n + n)
    Odd  :: The Peano n -> Parity (S (n + n))

parity :: The Peano n -> Parity n
parity Zy = Even Zy
parity (Sy Zy) = Odd Zy
parity (Sy (Sy n)) = case parity n of
  Even m -> gcastWith (plusSuccDistrib m m) (Even (Sy m))
  Odd  m -> gcastWith (plusSuccDistrib m m) (Odd (Sy m))

plusSuccDistrib :: The Peano n -> proxy m -> n + S m :~: S (n + m)
plusSuccDistrib Zy _ = Refl
plusSuccDistrib (Sy n) p = gcastWith (plusSuccDistrib n p) Refl
```

We need this function on the type-level, though, not the value-level: here, again, we run into trouble. What does `gcastWith`{.haskell} look like on the type-level? As far as I can tell, it doesn't exist (yet. Although I haven't looked deeply into the singletons library yet).

This idea of doing dependently-typed stuff on the type-level *started* to be possible with `TypeInType`{.haskell}. For instance, we could have defined our binary type as:

```{.haskell}
data Binary :: Peano -> Type where
    O :: Binary n -> Binary (n + n)
    I :: Binary n -> Binary (S (n + n))
    E :: Binary Z
```

And then the binomial heap as:

```{.haskell}
data Binomial (xs :: Binary n) (rk :: Peano) (a :: Type) where
       Nil :: Binomial E n a
       Skip :: Binomial xs (S rk) a -> Binomial (O xs) rk a
       (:-) :: Tree rk a 
            -> Binomial xs (S rk) a 
            -> Binomial (I xs) rk a
```

What we're doing here is indexing a type *by an indexed type*. [This wasn't possible in Haskell a few years ago](http://stackoverflow.com/a/13241158/4892417). It still doesn't get us a nice definition of subtraction, though.

### Using a Typechecker Plugin

It's pretty clear that this approach gets tedious almost immediately. What's more, if we want the proofs to be erased, we introduce potential for errors.

The solution? Beef up GHC's typechecker with a plugin. I first came across this approach in [Kenneth Foner's talk at Compose](https://www.youtube.com/watch?v=u_OsUlwkmBQ). He used a plugin that called out to the [Z3 theorem prover](https://github.com/Z3Prover/z3) [from @diatchki_improving_2015]; I'll use a [simpler plugin](https://hackage.haskell.org/package/ghc-typelits-natnormalise) which just normalizes type-literals.

From what I've used of these plugins so far, they seem to work really well. They're very unobtrusive, only requiring a pragma at the top of your file:

```{.haskell}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
```

The plugin is only called when GHC can't unify two types: this means you don't get odd-looking error messages in unrelated code (in fact, the error messages I've seen so far have been excellent—a real improvement on the standard error messages for type-level arithmetic). Another benefit is that we get to use type-level literals (`Nat`{.haskell} imported from [GHC.TypeLits](https://hackage.haskell.org/package/base-4.9.1.0/docs/GHC-TypeLits.html)), rather then the noisy-looking type-level Peano numbers. 

```{.haskell .literate}
data Tree n a = Root a (Node n a)

data Node :: Nat -> Type -> Type where
        NilN :: Node 0 a
        (:<) :: {-# UNPACK #-} !(Tree n a)
             -> Node n a
             -> Node (1 + n) a

mergeTree :: Ord a => Tree n a -> Tree n a -> Tree (1 + n) a
mergeTree xr@(Root x xs) yr@(Root y ys)
  | x <= y    = Root x (yr :< xs)
  | otherwise = Root y (xr :< ys)

infixr 5 :-
data Binomial :: Nat -> Nat -> Type -> Type where
        Nil  :: Binomial n 0 a
        (:-) :: {-# UNPACK #-} !(Tree z a)
             -> Binomial (1 + z) xs a
             -> Binomial z (1 + xs + xs) a
        Skip :: Binomial (1 + z) (1 + xs) a
             -> Binomial z (2 + xs + xs) a
```

This definition also ensures that the binomial heap has no trailing zeroes in its binary representation: the `Skip`{.haskell} constructor can only be applied to a heap bigger than zero.

Since we're going to be looking at several different heaps, we'll need a class to represent all of them:

```{.haskell .literate}
class IndexedQueue h a where

    {-# MINIMAL insert, empty, minViewMay, minView #-}

    empty
        :: h 0 a

    minView
        :: h (1 + n) a -> (a, h n a)

    singleton
        :: a -> h 1 a
    singleton = flip insert empty

    insert
        :: a -> h n a -> h (1 + n) a

    minViewMay
       :: h n a
       -> (n ~ 0 => b)
       -> (forall m. (1 + m) ~ n => a -> h m a -> b)
       -> b

class IndexedQueue h a =>
      MeldableIndexedQueue h a where
    merge
        :: h n a -> h m a -> h (n + m) a
```

You'll need `MultiParamTypeClasses`{.haskell} for this one.

```{.haskell .literate}
mergeB
    :: Ord a
    => Binomial z xs a -> Binomial z ys a -> Binomial z (xs + ys) a
mergeB Nil ys              = ys
mergeB xs Nil              = xs
mergeB (Skip xs) (Skip ys) = Skip (mergeB xs ys)
mergeB (Skip xs) (y :- ys) = y :- mergeB xs ys
mergeB (x :- xs) (Skip ys) = x :- mergeB xs ys
mergeB (x :- xs) (y :- ys) = Skip (mergeCarry (mergeTree x y) xs ys)

mergeCarry
    :: Ord a
    => Tree z a
    -> Binomial z xs a
    -> Binomial z ys a
    -> Binomial z (1 + xs + ys) a
mergeCarry !t Nil ys              = carryOne t ys
mergeCarry !t xs Nil              = carryOne t xs
mergeCarry !t (Skip xs) (Skip ys) = t :- mergeB xs ys
mergeCarry !t (Skip xs) (y :- ys) = Skip (mergeCarry (mergeTree t y) xs ys)
mergeCarry !t (x :- xs) (Skip ys) = Skip (mergeCarry (mergeTree t x) xs ys)
mergeCarry !t (x :- xs) (y :- ys) = t :- mergeCarry (mergeTree x y) xs ys

carryOne :: Ord a => Tree z a -> Binomial z xs a -> Binomial z (1 + xs) a
carryOne !t Nil       = t :- Nil
carryOne !t (Skip xs) = t :- xs
carryOne !t (x :- xs) = Skip (carryOne (mergeTree t x) xs)

instance Ord a => MeldableIndexedQueue (Binomial 0) a where
    merge = mergeB
    {-# INLINE merge #-}

instance Ord a => IndexedQueue (Binomial 0) a where
    empty = Nil
    singleton x = Root x NilN :- Nil
    insert = merge . singleton
```

(`BangPatterns`{.haskell} for this example)

On top of that, it's very easy to define delete-min:

```{.haskell .literate}
    minView xs = case minViewZip xs of
      Zipper x _ ys -> (x, ys)
    minViewMay q b f = case q of
      Nil -> b
      _ :- _ -> uncurry f (minView q)
      Skip _ -> uncurry f (minView q)

data Zipper a n rk = Zipper !a (Node rk a) (Binomial rk n a)

skip :: Binomial (1 + z) xs a -> Binomial z (xs + xs) a
skip x = case x of
  Nil    -> Nil
  Skip _ -> Skip x
  _ :- _ -> Skip x

data MinViewZipper a n rk where
    Infty :: MinViewZipper a 0 rk
    Min :: {-# UNPACK #-} !(Zipper a n rk) -> MinViewZipper a (n+1) rk

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
  size :: h n a -> The Peano n

instance Sized Heap where
  size E = Zy
  size (T _ xs) = Sy (size xs)

plus :: The Peano n -> The Peano m -> The Peano (n + m)
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

The typechecker plugin makes it relatively easy to implement several other heaps: skew, Braun, etc. You'll need one extra trick to implement a [leftist heap](http://lambda.jstolarek.com/2014/10/weight-biased-leftist-heaps-verified-in-haskell-using-dependent-types/), though. Let's take a look at the unverified version:

```{.haskell}
data Leftist a
    = Leaf
    | Node {-# UNPACK #-} !Int
           a
           (Leftist a)
           (Leftist a)

rank :: Leftist s -> Int
rank Leaf          = 0
rank (Node r _ _ _) = r
{-# INLINE rank #-}

mergeL :: Ord a => Leftist a -> Leftist a -> Leftist a
mergeL Leaf h2 = h2
mergeL h1 Leaf = h1
mergeL h1@(Node w1 p1 l1 r1) h2@(Node w2 p2 l2 r2)
  | p1 < p2 =
      if ll <= lr
          then LNode (w1 + w2) p1 l1 (mergeL r1 h2)
          else LNode (w1 + w2) p1 (mergeL r1 h2) l1
  | otherwise =
      if rl <= rr
          then LNode (w1 + w2) p2 l2 (mergeL r2 h1)
          else LNode (w1 + w2) p2 (mergeL r2 h1) l2
  where
    ll = rank r1 + w2
    lr = rank l1
    rl = rank r2 + w1
    rr = rank l2
```

In a weight-biased leftist heap, the left branch in any tree must have at least as many elements as the right branch. Ideally, we would encode that in the representation of size-indexed leftist heap:

```{.haskell .literate}
data Leftist n a where
        Leaf :: Leftist 0 a
        Node :: !(The Nat (n + m + 1))
             -> a
             -> Leftist n a
             -> Leftist m a
             -> !(m <= n)
             -> Leftist (n + m + 1) a

rank :: Leftist n s -> The Nat n
rank Leaf             = sing
rank (Node r _ _ _ _) = r
{-# INLINE rank #-}
```

Two problems, though: first of all, we need to be able to *compare* the sizes of two heaps, in the merge function. If we were using the type-level Peano numbers, this would be too slow. More importantly, though, we need the comparison to provide a *proof* of the ordering, so that we can use it in the resulting `Node`{.haskell} constructor.


### Integer-Backed Type-Level Numbers

In Agda, the Peano type is actually backed by Haskell's `Integer`{.haskell} at runtime. This allows compile-time proofs to be written about values which are calculated efficiently. We can mimic the same thing in Haskell with a newtype wrapper *around* `Integer`{.haskell} with a phantom `Peano`{.haskell} parameter, if we promise to never put an integer in which has a different value to its phantom value. We can make this promise a little more trustworthy if we don't export the newtype constructor.

```{.haskell .literate}
newtype instance The Nat n where
        NatSing :: Integer -> The Nat n

instance KnownNat n => KnownSing n where
    sing = NatSing $ Prelude.fromInteger $ natVal (Proxy :: Proxy n)
```

`FlexibleInstances`{.haskell} is needed for the instance. We can also encode all the necessary arithmetic:

```{.haskell .literate}
infixl 6 +.
(+.) :: The Nat n -> The Nat m -> The Nat (n + m)
(+.) =
    (coerce :: (Integer -> Integer -> Integer) 
            -> The Nat n -> The Nat m -> The Nat (n + m))
        (+)
{-# INLINE (+.) #-}
```

Finally, the compare function (`ScopedTypeVariables`{.haskell} for this):

```{.haskell .literate}
infix 4 <=.
(<=.) :: The Nat n -> The Nat m -> The Bool (n <=? m)
(<=.) (NatSing x :: The Nat n) (NatSing y :: The Nat m)
  | x <= y = 
      case (unsafeCoerce (Refl :: True :~: True) :: (n <=? m) :~: True) of
        Refl -> Truey
  | otherwise = 
      case (unsafeCoerce (Refl :: True :~: True) :: (n <=? m) :~: False) of
        Refl -> Falsy
{-# INLINE (<=.) #-}

totalOrder ::  p n -> q m -> (n <=? m) :~: False -> (m <=? n) :~: True
totalOrder (_ :: p n) (_ :: q m) Refl = 
    unsafeCoerce Refl :: (m <=? n) :~: True

type x <= y = (x <=? y) :~: True
```

It's worth mentioning that all of these functions are somewhat axiomatic: there's no checking of these definitions going on, and any later proofs are only correct in terms of these functions.

If we want our merge function to *really* look like the non-verified version, though, we'll have to mess around with the syntax a little.

### A Dependent if-then-else

When matching on a singleton, *within* the case-match, proof of the singleton's type is provided. For instance:

```{.haskell}
type family IfThenElse (c :: Bool) (true :: k) (false :: k) :: k
     where
        IfThenElse True true false = true
        IfThenElse False true false = false

intOrString :: The Bool cond -> IfThenElse cond Int String
intOrString Truey = 1
intOrString Falsy = "abc"
```

In Haskell, since we can overload the if-then-else construct (with `RebindableSyntax`{.haskell}), we can provide the same syntax, while hiding the dependent nature:

```{.haskell .literate}
ifThenElse :: The Bool c -> (c :~: True -> a) -> (c :~: False -> a) -> a
ifThenElse Truey t _ = t Refl
ifThenElse Falsy _ f = f Refl
```

### Verified Merge

Finally, then, we can write the implementation for merge, which looks almost *exactly* the same as the non-verified merge:

```{.haskell .literate}
instance Ord a => IndexedQueue Leftist a where

    minView (Node _ x l r _) = (x, merge l r)
    {-# INLINE minView #-}


    singleton x = Node sing x Leaf Leaf Refl
    {-# INLINE singleton #-}

    empty = Leaf
    {-# INLINE empty #-}

    insert = merge . singleton
    {-# INLINE insert #-}

    minViewMay Leaf b _             = b
    minViewMay (Node _ x l r _) _ f = f x (merge l r)

instance Ord a =>
         MeldableIndexedQueue Leftist a where
    merge Leaf h2 = h2
    merge h1 Leaf = h1
    merge h1@(Node w1 p1 l1 r1 _) h2@(Node w2 p2 l2 r2 _)
      | p1 < p2 =
          if ll <=. lr
             then Node (w1 +. w2) p1 l1 (merge r1 h2)
             else Node (w1 +. w2) p1 (merge r1 h2) l1 . totalOrder ll lr
      | otherwise =
          if rl <=. rr
              then Node (w1 +. w2) p2 l2 (merge r2 h1)
              else Node (w1 +. w2) p2 (merge r2 h1) l2 . totalOrder rl rr
      where
        ll = rank r1 +. w2
        lr = rank l1
        rl = rank r2 +. w1
        rr = rank l2
    {-# INLINE merge #-}
```

What's cool about this implementation is that it has the same performance as the non-verified version (if `Integer`{.haskell} is swapped out for `Int`{.haskell}, that is), and it *looks* pretty much the same. This is very close to static verification for free.

### Generalizing Sort to Parts

The `Sort`{.haskell} type used in the original blog post can be generalized to *any* indexed container. 

```{.haskell}
data Parts f g a b r where
    Parts :: (forall n. g (m + n) b -> (g n b, r))
         -> !(f m a)
         -> Parts f g a b r

instance Functor (Parts f g a b) where
  fmap f (Parts g h) =
    Parts (\h' -> case g h' of (remn, r) -> (remn, f r)) h
  {-# INLINE fmap #-}

instance (IndexedQueue f x, MeldableIndexedQueue f x) =>
          Applicative (Parts f g x y) where
    pure x = Parts (\h -> (h, x)) empty
    {-# INLINE pure #-}

    (Parts f (xs :: f m x) :: Parts f g x y (a -> b)) <*> 
      Parts g (ys :: f n x) =
        Parts h (merge xs ys)
        where
          h :: forall o . g ((m + n) + o) y -> (g o y, b)
          h v = case f v of { (v', a) ->
                    case g v' of { (v'', b) ->
                      (v'', a b)}}
    {-# INLINABLE (<*>) #-}

```

This version doesn't insist that you order the elements of the heap in any particular way: we could use indexed difference lists to reverse a container, or indexed lists to calculate permutations of a container, for instance.

### Other Uses For Size-Indexed Heaps

I'd be very interested to see any other uses of these indexed heaps, if anyone has any ideas. Potentially the could be used in any place where there is a need for some heap which is known to be of a certain size (a true prime sieve, for instance).

### The Library

I've explored all of these ideas [here](https://github.com/oisdk/type-indexed-queues). It has implementations of all the heaps I mentioned, as well as the index-erasing type, and a size-indexed list, for reversing traversables. In the future, I might add things like a Fibonacci heap, or the optimal Brodal/Okasaki heap [@brodal_optimal_1996].

---
