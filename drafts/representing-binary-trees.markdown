---
title: Representing Binary Trees
tags: Agda, Haskell
bibliography: Tree Conversion.bib
---

I've been playing around with some interesting algorithms and aspects of binary
trees.

```haskell
data Tree = Leaf | Tree :*: Tree
```

I thought I'd go through some of them today!

# Enumerating

As part of my master's thesis I needed to prove that one could only make
finitely many arithmetic expressions from list of numbers and binary operators,
and then enumerate them.
(It was part of writing a verified solver for the countdown problem).
There were a lot of interesting parts to the algorithm: enumerating
permutations, for instance, was particularly tricky.
Since not all of the binary operators were associative, however, I also needed
to enumerate all the binary trees of a given size; this problem has stuck with
me the most.

Apparently enumeration of binary trees is pretty well-studied, and an important
topic in combinatorics.
As I was writing the code in Agda, however, I needed an especially simple
algorithm that I could write proofs about (and one that was structurally
terminating).

For instance, if you use the standard algorithm presented in the first Countdown
paper [@hutton_countdown_2002], you'll run into issues with termination.
So I decided I wasn't going to attack the problem directly, and instead I'd look
for a type which was isomorphic with (or at least had surjection into) binary
trees.

In this search I came across Dyck words.

# Dyck Words

A "Dyck word" is a string of balanced parentheses.

```
()()
(()())()
(())()
```

There's a lot of interesting aspects to these strings, which we'll look at in
this post, but the important point for me was that I read that they were
*isomorphic* to the binary trees.
And, as a *flat* kind of data structure, strings seemed an awful lot easier to
enumerate than binary trees.

So let's get a type definition down for these strings, and see what we can do
with it.

```haskell
type Dyck = [Bool]
```

This particular type won't work at all.
It includes many values which *don't* represent balanced parentheses.
Instead we'll have to reach for the GADTs:

```haskell
data Dyck (n :: Nat) :: Type where
  Done :: Dyck Z
  Open :: Dyck (S n) -> Dyck n
  Clos :: Dyck n     -> Dyck (S n)
```

This type doesn't represent Dyck words exactly; it represents *suffixes* of
them.
Its parameter is the number of extraneous closing parentheses: in other words, a
value of type `Dyck Z` is a proper Dyck word.

```haskell
type Bal = Dyck Z
```

```haskell
>>> Open $ Clos $ Open $ Clos $ Done :: Bal
()()

>>> Open $ Open $ Clos $ Open $ Clos $ Clos $ Open $ Clos $ Done :: Bal
(()())()

>>> Open $ Open $ Clos $ Clos $ Open $ Clos $ Done :: Bal
(())()
```

The next task is to actually enumerate these words.
Here's an $O(n)$ algorithm which does just that:

```haskell
enumDyck :: Int -> [Bal]
enumDyck sz = go Zy sz Done []
  where
    go :: Natty n -> Int -> Dyck n -> [Bal] -> [Bal]
    go Zy     0 k = (:) k
    go (Sy n) 0 k = go n 0 (Open k)
    go Zy     m k = go (Sy Zy) (m-1) (Clos k)
    go (Sy n) m k =
      go n m (Open k) .
      go (Sy (Sy n)) (m-1) (Clos k)
      
>>> mapM_ print (enumDyck 3)
"()()()"
"(())()"
"()(())"
"(()())"
"((()))"
```

A variant of this function was what I needed in my thesis: I also needed to
prove that it produced every possible value of the type `Dyck n`, which was not
too difficult.

In Haskell, enumeration is still quite useful, for things like QuickCheck.
In particular, this function can be adapted to efficiently produce random Dyck
words:

```haskell
genDyck :: Natty n -> Int -> (Dyck n -> Gen a) -> Gen a
genDyck Zy     0 k = k Done 
genDyck (Sy n) 0 k = genDyck n 0 (k . Clos)
genDyck Zy     m k = genDyck (Sy Zy) (m-1) (k . Open)
genDyck (Sy n) m k = do
  bit <- arbitrary
  if bit then genDyck n m (k . Clos) else genDyck (Sy (Sy n)) (m-1) (k . Open)

instance Arbitrary Bal where
  arbitrary = sized (flip (genDyck Zy) pure)
```

I am pretty sure that this generates random Dyck words with the minimum number
of random bits, but I have not proven that yet.

But enough of that: now we need to convert between this type and a binary tree.

# Conversion

First, for the conversion algorithms we'll actually need another GADT:

```haskell
infixr 5 :-
data Stack (a :: Type) (n :: Nat) :: Type where
  Nil  :: Stack a Z
  (:-) :: a -> Stack a n -> Stack a (S n)
```

The familiar length-indexed vector will be extremely useful for the next few
bits of code: it will act as a stack in our stack-based algorithms.
Here's one of those algorithms now:

```haskell
dyckToTree :: Bal -> Tree
dyckToTree dy = go dy (Leaf :- Nil)
  where
    go :: Dyck n -> Stack Tree (S n) -> Tree
    go (Open d) ts               = go d (Leaf :- ts)
    go (Clos d) (t1 :- t2 :- ts) = go d (t2 :*: t1 :- ts)
    go Done     (t  :- Nil)      = t
```

This might be familiar: it's actually shift-reduce parsing dressed up with some
types.
The nice thing about it is that it's completely total: all pattern-matches are
accounted for here, and when written in Agda it's clearly structurally
terminating.

The function in the other direction is similarly simple:

```haskell
treeToDyck :: Tree -> Bal
treeToDyck t = go t Done
  where
    go :: Tree -> Dyck n -> Dyck n
    go Leaf        = id
    go (xs :*: ys) = go xs . Open . go ys . Clos
```

And, we can use our arbitrary instance to test the isomorphism in one direction
at least:

```haskell
roundTrip :: Bal -> Property
roundTrip d = treeToDyck (dyckToTree d) === d
```

# A Compiler

Much of this stuff has been on my mind recently because of
[this](https://www.youtube.com/watch?v=T_IINWzQhow) [-@riley_program_2020] video
on the computerphile channel, in which Graham Hutton goes through using
QuickCheck to test an interesting compiler.
The compiler itself is explored more in depth in @bahr_calculating_2015, where
the algorithms developed are really quite similar to those that we have here.

The advantage of the code above is that it's all *total*: we will never pop
items off the stack that aren't there.
This is a nice addition, and it's surprisingly simple to add: let's see if we
can add it to the compiler presented in the paper.

The first thing we need to change is we need to add a payload to our tree type:
the one above is just the *shape* of a binary tree, but the language presented
in the paper contains values.

```haskell
data Expr (a :: Type) where
  Val   :: a -> Expr a
  (:+:) :: Expr a -> Expr a -> Expr a
```

We'll need to change the definition of `Dyck` similarly:

```haskell
data Code (n :: Nat) (a :: Type) :: Type where
  HALT :: Code (S Z) a
  PUSH :: a -> Code (S n) a -> Code n a
  ADD  :: Code (S n) a -> Code (S (S n)) a
```

After making it so that these data structures can now store contents, there are
two other changes worth pointing out:

* The names have been changed, to match those in the paper.
  It's a little clearer now that the Dyck word is a bit like code for a simple
  stack machine.
* The numbering on `Code` has changed.
  Now, the `HALT` constructor has a parameter of `1` (well, `S Z`), where its
  corresponding constructor in `Dyck` (`Done`) had `0`.
  Why is this?
  I am not entirely sure!
  To get this stuff to all work out nicely took a huge amount of trial and
  error, I would love to see a more principled reason why the numbering changed
  here.
  
With these definitions we can actually transcribe the `exec` and `comp`
functions almost verbatim [from page 11 and 12 of -@bahr_calculating_2015].

```haskell
exec :: Code n Int -> Stack Int (n + m) -> Stack Int (S m)
exec HALT         st              = st
exec (PUSH v is)  st              = exec is (v :- st)
exec (ADD    is) (t1 :- t2 :- st) = exec is (t2 + t1 :- st)

comp :: Expr a -> Code Z a
comp e = comp' e HALT
  where
    comp' :: Expr a -> Code (S n) a -> Code n a
    comp' (Val     x) = PUSH x
    comp' (xs :+: ys) = comp' xs . comp' ys . ADD
```

# Proving the Isomorphism

As I have mentioned, a big benefit of all of this stuff is that it can be
translated into Agda readily.
The real benefit of *that* is that we can show the two representations of
programs are fully isomorphic.
I have proven this
[here](https://github.com/oisdk/agda-playground/blob/d7234c276f063dbb4a2d2cbcedb86dd48501a908/Data/Dyck/Payload.agda):
the proof is surprisingly short (about 20 lines), and the rest of the code
follows the Haskell stuff quite closely.
I got the idea for much of the proof from
[this](https://gist.github.com/Boarders/9d83f9cbcfaffb04cf2464588fc46df9) bit of
code by [Callan McGill](https://boarders.github.io/) [-@mcgill_compiler_2020].

I'll include it here as a reference.

<details>
<summary>Agda Code</summary>

```agda
open import Prelude
open import Data.Nat using (_+_)
open import Data.Vec.Iterated using (Vec; _∷_; []; foldlN; head)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- Binary trees: definition and associated functions
--------------------------------------------------------------------------------

data Tree (A : Type a) : Type a where
  [_] : A → Tree A
  _*_ : Tree A → Tree A → Tree A

--------------------------------------------------------------------------------
-- Programs: definition and associated functions
--------------------------------------------------------------------------------

data Prog (A : Type a) : ℕ → Type a where
  halt : Prog A 1
  push : A → Prog A (1 + n) → Prog A n
  pull : Prog A (1 + n) → Prog A (2 + n)

--------------------------------------------------------------------------------
-- Conversion from a Prog to a Tree
--------------------------------------------------------------------------------

prog→tree⊙ : Prog A n → Vec (Tree A) n → Tree A
prog→tree⊙ halt        (v ∷ [])       = v
prog→tree⊙ (push v is) st             = prog→tree⊙ is ([ v ] ∷ st)
prog→tree⊙ (pull   is) (t₁ ∷ t₂ ∷ st) = prog→tree⊙ is (t₂ * t₁ ∷ st)

prog→tree : Prog A zero → Tree A
prog→tree ds = prog→tree⊙ ds []

--------------------------------------------------------------------------------
-- Conversion from a Tree to a Prog
--------------------------------------------------------------------------------

tree→prog⊙ : Tree A → Prog A (suc n) → Prog A n
tree→prog⊙ [ x ]     = push x
tree→prog⊙ (xs * ys) = tree→prog⊙ xs ∘ tree→prog⊙ ys ∘ pull

tree→prog : Tree A → Prog A zero
tree→prog tr = tree→prog⊙ tr halt

--------------------------------------------------------------------------------
-- Proof of isomorphism
--------------------------------------------------------------------------------

tree→prog→tree⊙ : (e : Tree A) (is : Prog A (1 + n)) (st : Vec (Tree A) n) →
  prog→tree⊙ (tree→prog⊙ e is) st ≡ prog→tree⊙ is (e ∷ st)
tree→prog→tree⊙ [ x ]     is st = refl
tree→prog→tree⊙ (xs * ys) is st = tree→prog→tree⊙ xs _ st ;
                                  tree→prog→tree⊙ ys (pull is) (xs ∷ st)

tree→prog→tree : (e : Tree A) → prog→tree (tree→prog e) ≡ e
tree→prog→tree e = tree→prog→tree⊙ e halt []

prog→tree→prog⊙ : (is : Prog A n) (st : Vec (Tree A) n) →
 tree→prog (prog→tree⊙ is st) ≡ foldlN (Prog A) tree→prog⊙ is st
prog→tree→prog⊙  halt       st = refl
prog→tree→prog⊙ (push i is) st = prog→tree→prog⊙ is ([ i ] ∷ st)
prog→tree→prog⊙ (pull is) (t₁ ∷ t₂ ∷ ts) = prog→tree→prog⊙ is ((t₂ * t₁) ∷ ts)

prog→tree→prog : (is : Prog A 0) → tree→prog (prog→tree is) ≡ is
prog→tree→prog is = prog→tree→prog⊙ is []

prog-iso : Prog A zero ⇔ Tree A
prog-iso .fun = prog→tree
prog-iso .inv = tree→prog
prog-iso .rightInv = tree→prog→tree
prog-iso .leftInv  = prog→tree→prog
```

</details>

# Future Thoughts

I think that's enough for one post!
One last thing I'll mention is that all of the `exec` functions presented
are *folds*.
In particular, they're *left* folds.
Here's how we'd rewrite `exec` to make that fact clear:

```haskell
foldlCode :: (∀ n. a -> b n -> b (S n))
          -> (∀ n. b (S (S n)) -> b (S n))
          -> b m
          -> Code m a -> b (S Z)
foldlCode _ _ h  HALT       = h
foldlCode p a h (PUSH x xs) = foldlCode p a (p x h) xs
foldlCode p a h (ADD    xs) = foldlCode p a (a   h) xs

shift :: Int -> Stack Int n -> Stack Int (S n)
shift x xs = x :- xs

reduce :: Stack Int (S (S n)) -> Stack Int (S n)
reduce (t1 :- t2 :- st) = t2 + t1 :- st

execFold :: Code Z Int -> Int
execFold = pop . foldlCode shift reduce Nil
```

I think the "foldl-from-foldr" trick could be a nice way to explain the
introduction of continuations in @bahr_calculating_2015.

# Code

As I mentioned, the Agda code for this stuff can be found
[here](https://github.com/oisdk/agda-playground/blob/d7234c276f063dbb4a2d2cbcedb86dd48501a908/Data/Dyck/Payload.agda),
I have also put all of the Haskell code in one place
[here](https://gist.github.com/oisdk/438b6e790481c908d9460ffb1196a759).

Also, with all of this we can finally write a direct algorithm for efficient
enumeration of binary trees:

```haskell
trees :: [a] -> Tree (Tree a)
trees []     = error "trees needs to be given a non-empty list"
trees (x:xs) = foldr f b xs (Leaf x) []
  where
    b t st = Leaf (foldl (flip (:*:)) t st)
    
    f v k t st = g v k t st (k (Leaf v) (t : st))
    
    g v k t1 (t2 : st) o = o :*: f v k (t2 :*: t1) st
    g _ _ _  []        o = o
```

From this we can also write a nice method for efficiently generating random trees:

```haskell
instance Arbitrary a => Arbitrary (Tree a) where
  arbitrary = choice . trees . getNonEmpty =<< arbitrary
    where
      choice (Leaf x) = pure x
      choice (xs :*: ys) = arbitrary >>= bool (choice xs) (choice ys)
      
  shrink (Leaf _)    = []
  shrink (xs :*: ys) = xs : ys : map (uncurry (:*:)) (shrink (xs,ys))
```

# References
