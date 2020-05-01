---
title: More Random Access Lists
series: Random Access Lists
tags: Haskell, Agda
bibliography: Random Access Lists.bib
---

<details>
<summary>
Imports and Pragmas
</summary>

```haskell
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE ScopedTypeVariables    #-}

{-# OPTIONS_GHC -Wall -fno-warn-unticked-promoted-constructors #-}

import Data.Kind
import Prelude hiding (lookup)
import GHC.TypeLits
```
</details>

# Numerical Representations

One of the common techniques for building purely functional data structures is
to base the structure on some numerical representation [@hinze_numerical_1998].
Most recently, I read @swierstraHeterogeneousBinaryRandomaccess2020, where the
binary numbers were used to implement a heterogeneous random-access list
(effectively a generic tuple).

I'm going to look today at using the zeroless binary system to implement a
similar structure, and see what the differences are.

# Zeroless Binary

I have talked about this representation before, so I won't go into it in huge
depth, but put simply the zeroless binary system represents a binary number as a
string of `1`s and `2`s (i.e. no zeroes).
The vast majority of the normal binary operations (addition, multiplication,
etc.) can be implemented with the same broad efficiency, but this system has one
key advantage in that every single number is uniquely represented.
Since we're going to use these numbers to index our data types, this is actually
extremely useful.

Before we get started, we'll first define the peculiar type of lists we're going
to use.

```haskell
infixr 5 :-
data Plus a = a :- Star a
data Star a
  = Nil
  | Some (Plus a)
```

`Star a` is isomorphic to `[a]`, so we're not actually using something much
different.
The usefulness of this definition is that we have a non-empty list type built
in to our list type, so we don't have to do conversion back and forth which can
be cumbersome.

Next on to the number itself:

```haskell
data Bit = B1 | B2

type family Inc (xs :: Star Bit) = (ys :: Plus Bit) | ys -> xs where
  Inc Nil = B1 :- Nil
  Inc (Some (B1 :- xs)) = B2 :- xs
  Inc (Some (B2 :- xs)) = B1 :- Some (Inc xs)
```

We're straight into the type-level operations here, and there's an interesting
bit of syntax worth pointing out before we move on.
`ys -> xs` is a type family dependency: it means that we can uniquely determine
`xs` given `ys`.
This is very handy for type inference and so on, and is perhaps the main benefit
of the zeroless binary numbers.

# A Braun Tree

Next, we'll build a tree indexed by these numbers.
Now that we're jumping in to indexing, we'll need some singletons.
Here's my preferred way to do them:

```haskell
type family The k = (s :: k -> Type) | s -> k

class Known (x :: a) where sing :: The a x

data SBit b where
  SB1 :: SBit B1
  SB2 :: SBit B2
  
type instance The Bit = SBit
instance Known B1 where sing = SB1
instance Known B2 where sing = SB2
```

The type family defines the singleton GADTs themselves.
The class `Known` is for automatically generating singleton values.

On to the tree.
We're actually going to build a *Braun* tree here, as they are actually
particularly clean to implement on the type level.

```haskell
type family Carry (x :: Bit) (xs :: Star Bit) :: Star Bit where
  Carry B1 xs = xs
  Carry B2 xs = Some (Inc xs)
  
data Tree (xs :: Star Bit) a where
  Leaf   :: Tree Nil a
  Branch :: Forest xs a -> Tree (Some xs) a

data Forest (xs :: Plus Bit) a where
  Root :: a
       -> The Bit x 
       -> Tree (Carry x xs) a 
       -> Tree xs a 
       -> Forest (x :- xs) a
```

We first have a type family which increments a binary number if its first
argument is `B2`: this will maintain the Braun tree's invariant.

Next, we have the tree definition itself, which is split into two mutual
definitions, in much the same way as the `Star` and `Plus` lists previously.
Next, to `cons` something onto the tree:

```haskell
type family Cons (x :: a) (xs :: Tree ns a) = (ys :: Forest (Inc ns) a) | ys -> x xs where
  Cons x Leaf = Root x SB1 Leaf Leaf
  Cons x (Branch (Root y SB1 ls rs)) = Root x SB2 (Branch (Cons y rs)) ls
  Cons x (Branch (Root y SB2 ls rs)) = Root x SB1 (Branch (Cons y rs)) ls
```

You'll notice that we can again annotate this type family with injectivity.

# A Heterogeneous Tree

So far all we have is a size-indexed tree.
We want a *heterogeneous* tree, meaning that we must next construct a tree
*indexed* by the previous tree.
In order to do this, we'll first need singletons on the type level:

```haskell
type family Sing (x :: a) = (y :: The a x) | y -> x
type instance Sing B1 = SB1
type instance Sing B2 = SB2
```

This kind of nonsense we're doing here is precisely the kind of thing obfuscated
by dependent types, by the way.
If you're already doing type-level heavy stuff (as we are here) the extra power
afforded by full dependent types often means that hacky special cases just turn
into standard functions, greatly simplifying things like the above type
families.

But anyway, back to the tree:

```haskell
data HTree (xs :: Tree ns Type) where
  HLeaf :: HTree Leaf
  HNode :: x 
        -> !(The Bit b) 
        -> !(HTree ls)
        -> !(HTree rs)
        -> HTree (Branch (Root x (Sing b) ls rs))
```

And we can `cons` on an element in much the same way we did with the homogeneous
tree:

```haskell
infixr 5 <:
(<:) :: x -> HTree xs -> HTree (Branch (Cons x xs))
x <: HLeaf = HNode x SB1 HLeaf HLeaf
x <: HNode y SB1 yl yr = HNode x SB2 (y <: yr) yl
x <: HNode y SB2 yl yr = HNode x SB1 (y <: yr) yl
```

# Indexing

The real use of this data structure is quick *indexing*.
As with the previous functions, we will first need to construct the type-level
version of what we want to do.

```haskell
type family Lookup (i :: Star Bit) (xs :: Tree sz a) :: a where
  Lookup Nil              (Branch (Root x _ _  _)) = x
  Lookup (Some (B1 :- i)) (Branch (Root _ _ ls _)) = Lookup i ls
  Lookup (Some (B2 :- i)) (Branch (Root _ _ _ rs)) = Lookup i rs
```

While this function is partial, the value-level one should not be: it should be
provably in-bounds for lookups.
As a result we'll need a slightly complex type to represent the indices:

```haskell
data Position (xs :: Star Bit) (ys :: Star Bit) where
  P0 :: Position Nil (Some ys)
  P1 :: !(Position xs (Carry y ys)) -> Position (Some (B1 :- xs)) (Some (y :- ys))
  P2 :: !(Position xs ys) -> Position (Some (B2  :- xs)) (Some (y :- ys))
```

A value of type `Position xs ys` is actually a proof that `xs` is smaller than
`ys`, but we're using it here just as a pointer to an entry in the tree.
Here's the actual lookup function itself.

```haskell
lookup :: forall is (ts :: Tree sz Type). Position is sz -> HTree ts -> Lookup is ts
lookup P0     (HNode x _ _  _) = x
lookup (P1 i) (HNode _ _ ls _) = lookup i ls
lookup (P2 i) (HNode _ _ _ rs) = lookup i rs
```

Just having pointers isn't much use: we also need a way to build them.
The key function here is `push`: this increments the index pointed to by one.

<details>
<summary>
Singletons for lists
</summary>

```haskell
infixr 5 ::-
data SPlus xs where
  (::-) :: The a x -> The (Star a) xs -> SPlus (x :- xs)
  
data SStar xs where
  Nily :: SStar Nil
  Somy :: The (Plus a) xs -> SStar (Some xs)
  
type instance The (Plus a) = SPlus
type instance The (Star a) = SStar

instance Known Nil where sing = Nily
instance Known xs => Known (Some xs) where sing = Somy sing
instance (Known x, Known xs) => Known (x :- xs) where sing = sing ::- sing
```

</details>

```haskell
push :: Known ys => Position xs ys -> Position (Some (Inc xs)) (Some (Inc ys))
push p = go p sing
  where
    go :: Position xs ys -> The (Star Bit) ys -> Position (Some (Inc xs)) (Some (Inc ys))
    go P0     (Somy (SB1 ::- _ )) = P1 P0
    go P0     (Somy (SB2 ::- _ )) = P1 P0
    go (P2 i) (Somy (SB1 ::- ys)) = P1 (go i ys)
    go (P2 i) (Somy (SB2 ::- ys)) = P1 (go i ys)
    go (P1 i) (Somy (SB1 ::- _ )) = P2 i
    go (P1 i) (Somy (SB2 ::- _ )) = P2 i
```

# Type-Level Lists for A Nicer Interface

Everything above is pretty much all you need for many use cases, but it's pretty
ugly stuff.
To actually use this thing as a generic tuple we'll need a lot of
quality-of-life improvements.

First of all, we should use type-level lists to indicate the tuple itself:

<details>
<summary>
Type families for building a tree from a list.
</summary>

```haskell
type family Length (xs :: [a]) :: Star Bit where
  Length '[] = Nil
  Length (_ : xs) = Some (Inc (Length xs))
  
type family FromList (xs :: [a]) = (ys :: Tree (Length xs) a) | ys -> xs where
  FromList '[] = Leaf
  FromList (x : xs) = Branch (Cons x (FromList xs))
```
</details>

```haskell
type family Tuple (xs :: [Type]) = (ys :: Type) | ys -> xs where
  Tuple xs = HTree (FromList xs)
```

Because the type family here is injective, we won't get any of the usual weird
errors when we use the type `Tuple [Bool,String]`{.haskell} or whatever: passing
that around will function almost exactly the same as passing around the tree
representation itself directly.

```haskell
example :: Tuple [Bool,String,Int,(),String]
example = True <: "True" <: 1 <: () <: "T" <: HLeaf
```

# Folding

We can fold over the tree itself (using the Braun tree folding
algorithm from a previous post) if every element in the tree conforms to some
class.
Using this we can generate a nice string representation of the tree.

<details>
<summary>
Implementation of folding over tree and `Show` instance.
</summary>
  
```haskell
type family All (c :: a -> Constraint) (xs :: Tree ns a) :: Constraint where
  All c Leaf = ()
  All c (Branch (Root x _ ls rs)) = (c x, All c ls, All c rs)
  
newtype Q2 a
  = Q2
  { unQ2 :: (Q2 a -> Q2 a) -> (Q2 a -> Q2 a) -> a
  }

foldrTree :: forall c xs b. All c xs => (forall x. c x => x -> b -> b) -> b -> HTree xs -> b
foldrTree g' n' t = unQ2 (f @c g' n' t b) id id
  where
    f :: forall c' ys b'. All c' ys => (forall x. c' x => x -> b' -> b') -> b' -> HTree ys -> Q2 b' -> Q2 b'
    f g n (HNode x _ l r) xs = Q2 (\ls rs -> g x (unQ2 xs (ls . f @c' g n l) (rs . f @c' g n r)))
    f _ n HLeaf           _  = Q2 (\_  _  -> n)

    b = Q2 (\ls rs -> unQ2 (ls (rs b)) id id)

instance All Show xs => Show (HTree xs) where
  showsPrec _ tr = showChar '(' . go (foldrTree @Show (\x xs -> shows x : xs) [] tr)
    where
      go :: [ShowS] -> ShowS
      go []     = showChar ')'
      go (x:xs) = x . foldr (\y ys -> showChar ',' . y . ys)  (showChar ')') xs
```
</details>

```haskell
>>> example
(True,"True",1,(),"T")
```


# Using a Different Approach For Building Indices

The approach used in @swierstraHeterogeneousBinaryRandomaccess2020 had a
specific goal in mind: using the heterogeneous list to implement a lookup table
for evaluating lambda calculus.
As such, efficiently being able to "increment" an index was vital.

If we wanted to use the type as a generic tuple, though, we would have no such
requirement.
Instead, we might expect all accesses to be resolved and inlined at compile-time
[as in @martinezJustItCompiling2013] (we also would need to add INLINE pragmas
to every instance, which I haven't done here for readability's sake).
We also would want a nice syntax for accessing parts of the tuple.

We can accomplish all of this with some type classes, as it happens.
If we replace pattern-matching on data types with typeclass resolution we can be
all but guaranteed that the function calls and so on will be inlined entirely at
compile-time.
The main class we'll use is the following:

```haskell
class (xs :: Star Bit) < (ys :: Star Bit) where
  pull :: forall (t :: Tree ys Type). HTree t -> Lookup xs t
```

<details>
<summary>
Interface for building indices.
</summary>
  
```haskell
instance Nil < Some ys where
  pull (HNode x _ _ _) = x
  
instance xs < ys => Some (B1 :- xs) < Some (B1 :- ys) where
  pull (HNode _ _ ls _) = pull @xs ls
  
instance xs < Some (Inc ys) => Some (B1 :- xs) < Some (B2 :- ys) where
  pull (HNode _ _ ls _) = pull @xs ls

instance xs < ys => Some (B2 :- xs) < Some (y :- ys) where
  pull (HNode _ _ _ rs) = pull @xs rs

instance TypeError (Text "Index out of range") => xs < Nil where 
  pull = error "unreachable"

data Peano = Z | S Peano

type family FromPeano (n :: Peano) = (m :: Star Bit) | m -> n where
  FromPeano Z     = Nil
  FromPeano (S n) = Some (Inc (FromPeano n))
  
type family FromLit (n :: Nat) :: Peano where
  FromLit 0 = Z
  FromLit n = S (FromLit (n - 1))

get :: forall n xs (t :: Tree xs Type). FromPeano (FromLit n) < xs
    => HTree t -> Lookup (FromPeano (FromLit n)) t
get = pull @(FromPeano (FromLit n))
```
</details>

Some other details out of the way we get the following nice interface:

```haskell
>>> get @4 example
"T"
```

You even get a type error for out-of-range indices:

```haskell
>>> get @7 example
```
```
    • Index out of range
    • In the expression: get @7 example
      In an equation for ‘it’: it = get @7 example
```

Or we could even add a lens interface:

<details>
<summary>
Implementation of Lenses for the Tuple
</summary>

```haskell
type family Replace (i :: Star Bit) (x :: a) (xs :: Tree sz a) :: Tree sz a where
  Replace Nil              x (Branch (Root _ b ls rs)) = Branch (Root x b ls rs)
  Replace (Some (B1 :- i)) x (Branch (Root y b ls rs)) = Branch (Root y b (Replace i x ls) rs)
  Replace (Some (B2 :- i)) x (Branch (Root y b ls rs)) = Branch (Root y b ls (Replace i x rs))

class (xs :: Star Bit) <! (ys :: Star Bit) where
  index :: forall (t :: Tree ys Type) b. Lens (HTree t) (HTree (Replace xs b t)) (Lookup xs t) b
  
instance Nil <! Some ys where
  index f (HNode x b ls rs) = fmap (\x' -> HNode x' b ls rs) (f x)
  
instance xs <! ys => Some (B1 :- xs) <! Some (B1 :- ys) where
  index f (HNode x b ls rs) = fmap (\ls' -> HNode x b ls' rs) (index @xs f ls)
  
instance xs <! Some (Inc ys) => Some (B1 :- xs) <! Some (B2 :- ys) where
  index f (HNode x b ls rs) = fmap (\ls' -> HNode x b ls' rs) (index @xs f ls)

instance xs <! ys => Some (B2 :- xs) <! Some (y :- ys) where
  index f (HNode x b ls rs) = fmap (\rs' -> HNode x b ls rs') (index @xs f rs)

instance TypeError (Text "Index out of range") => xs <! Nil where 
  index = error "unreachable"

ind :: forall n xs (t :: Tree xs Type) a. FromPeano (FromLit n) <! xs
    => Lens (HTree t) (HTree (Replace (FromPeano (FromLit n)) a t)) (Lookup (FromPeano (FromLit n)) t) a
ind = index @(FromPeano (FromLit n))
```
</details>

```haskell
>>> over (ind @1) reverse example
(True,"eurT",1,(),"T")
```

# Usability

I actually am a little ambivalent about the "compile-time" stuff:
approaches like this one [and -@martinezJustItCompiling2013] tend to *really*
blow up compile times, and generate ugly, complex error messages.
@swierstraHeterogeneousBinaryRandomaccess2020 had a use case which actually
required a fast heterogeneous list, but if you're just looking for a tuple with
some fields and you need it to be fast you're probably better off with a one-off
data type.

That said, I do think Braun trees are excellent for this stuff, precisely
because they tend to be a little more usable in practice.
Their structure is uniquely determined by the number of elements they contain,
so all of the type families are injective, there's not a huge amount of
bookkeeping data, and they're just quite clean and simple.

---

# As a Nested Datatype

The approach I've taken here is actually a little unusual: in both
@hinze_numerical_1998 and
@swierstraHeterogeneousBinaryRandomaccess2020 the tree is defined as a *nested*
data type.
Let's take a look at that approach, while also switching to Agda. 

```agda
𝔹 : Set
𝔹 = List Bool

pattern 1ᵇ = false
pattern 2ᵇ = true

data When (A : Set a) : Bool → Set a where
  O⟨⟩ : When A false
  I⟨_⟩ : A → When A true

infixl 4 _×2
record _×2 (A : Set a) : Set a where
  constructor _,_
  field
    fst snd : A
open _×2

infixr 5 ⟨_⟩+_+2×_
data Array (A : Set a) : 𝔹 → Set a where
  O : Array A []
  ⟨_⟩+_+2×_ : ∀ {n ns} → A → When A n → Array (A ×2) ns → Array A (n ∷ ns)
```

The cons function here is really no more complex than the previous cons:

```agda
inc : 𝔹 → List Bool
inc [] = 1ᵇ ∷ []
inc (1ᵇ ∷ xs) = 2ᵇ ∷ xs
inc (2ᵇ ∷ xs) = 1ᵇ ∷ inc xs

cons : ∀ {ns} → A → Array A ns → Array A (inc ns)
cons x O = ⟨ x ⟩+ O⟨⟩ +2× O
cons x₁ (⟨ x₂ ⟩+ O⟨⟩ +2× xs) = ⟨ x₁ ⟩+ I⟨ x₂ ⟩ +2× xs
cons x₁ (⟨ x₂ ⟩+ I⟨ x₃ ⟩ +2× xs) = ⟨ x₁ ⟩+ O⟨⟩ +2× cons (x₂ , x₃) xs
```

But what I'm really interested in, again, is *indexing*.
In particular, I'm interested in using an actual binary number to index into
this structure, rather than the weird GADT we had to use in Haskell.
One of the advantages of using full dependent types is that we can write
functions like the following:


```agda
lookup : ∀ is → Array A xs → is < xs → A
lookup = {!!}
```

In other words, we can pass the proof term separately.
This can help performance a little, but mainly it's nice to use the actual
number type one intended to use along with all of the functions we might use on
that term.

So let's get writing!
The first thing to define is the proof of `<`.
I'm going to define it in terms of a boolean function on the bits themselves,
i.e.:

```agda
_<ᴮ_ : 𝔹 → 𝔹 → Bool
_<ᴮ_ = {!!}

T : Bool → Set
T true   = ⊤
T false  = ⊥

_<_ : 𝔹 → 𝔹 → Set
x < y = T (x <ᴮ y)
```

This will mean the proofs themselves are easy to pass around without
modification.
In fact, we can go further and have the compiler *definitionally* understand
that the proof of `x < y` is proof irrelevant, with Agda's
[`Prop`](https://agda.readthedocs.io/en/v2.6.1/language/prop.html).

```agda
_<_ : 𝔹 → 𝔹 → Set
x < y = T (x <ᴮ y)
```

Next, the actual function itself:

```agda
_&_≲ᵇ_ : Bool → Bool → Bool → Bool
s & false ≲ᵇ y = s or  y
s & true  ≲ᵇ y = s and y

_&_≲ᴮ_ : Bool → 𝔹 → 𝔹 → Bool
s & []       ≲ᴮ []       = s
s & []       ≲ᴮ (y ∷ ys) = true
s & (x ∷ xs) ≲ᴮ []       = false
s & (x ∷ xs) ≲ᴮ (y ∷ ys) = (s & x ≲ᵇ y) & xs ≲ᴮ ys

_<ᴮ_ _≤ᴮ_ : 𝔹 → 𝔹 → Bool
_<ᴮ_ = false &_≲ᴮ_
_≤ᴮ_ = true  &_≲ᴮ_
```

These functions combine the definitions of `≤` and `<`, and do them both at
once.
We pass whether the comparison is non-strict or not as the first parameter: this
is worth doing since both `<` and `≤` can be defined in terms of each other:

```agda
(1ᵇ ∷ xs) < (2ᵇ ∷ ys) = xs ≤ ys
(2ᵇ ∷ xs) ≤ (1ᵇ ∷ ys) = xs < ys
...
```

Finally the function itself:

```agda
sel-bit : ∀ {b} → When A b → A ×2 → A
sel-bit {b = 1ᵇ} _ = snd
sel-bit {b = 2ᵇ} _ = fst

mutual
  index : ∀ xs {ys} → Array A ys → xs < ys → A
  index []        (⟨ x ⟩+ _ +2× _ ) p = x
  index (1ᵇ ∷ is) (⟨ _ ⟩+ x +2× xs) p = index₂ is x xs p
  index (2ᵇ ∷ is) (⟨ _ ⟩+ x +2× xs) p = sel-bit x (index is xs p)

  index₂ : ∀ xs {y ys} → When A y → Array (A ×2) ys → 1ᵇ ∷ xs < y ∷ ys → A
  index₂ is       O⟨⟩    xs p = fst (index  is xs p)
  index₂ []       I⟨ x ⟩ xs p = x
  index₂ (i ∷ is) I⟨ _ ⟩ xs p = snd (index₃ i is xs p)

  index₃ : ∀ x xs {ys} → Array A ys → x ∷ xs ≤ ys → A
  index₃ 2ᵇ is       (⟨ _ ⟩+ x +2× xs) p = index₂ is x xs p
  index₃ 1ᵇ []       (⟨ x ⟩+ _ +2× _ ) p = x
  index₃ 1ᵇ (i ∷ is) (⟨ _ ⟩+ x +2× xs) p = sel-bit x (index₃ i is xs p)
```
