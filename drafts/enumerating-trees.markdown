---
title: Enumerating Trees
tags: Agda, Haskell
bibliography: Tree Conversion.bib
---

Consider the following puzzle: 

> Given a list of $n$ labels, list all the trees with those labels in order.

For instance, given the labels [1,2,3,4], the answer (for binary trees) is the
following:

```
┌1     ┌1      ┌1     ┌1     ┌1
┤      ┤      ┌┤     ┌┤     ┌┤
│┌2    │ ┌2   ││┌2   │└2    │└2
└┤     │┌┤    │└┤    ┤     ┌┤
 │┌3   ││└3   │ └3   │┌3   │└3
 └┤    └┤     ┤      └┤    ┤
  └4    └4    └4      └4   └4
```

This problem (the "enumeration" problem) turns out to be quite fascinating and
deep, with connections to parsing, monoids, and continuations.
It's also just a classic algorithmic problem which is fun to try and solve.

It's worth having a go at attempting it yourself, but if you'd just like to see
the slick solutions the following is one I'm especially proud of:

<details>
<summary>Solution to the Enumeration Problem on Forests of Rose Trees</summary>
```haskell
enumForests :: [a] -> [Forest a]
enumForests = foldrM f []
  where
    f x xs = zipWith ((:) . (:&) x) (inits xs) (tails xs)
```
</details>

In the rest of this post I'll go through the intuition behind solutions like the
one above and I'll try to elucidate some of the connections to other areas of
computer science.


# A First Approach: Trying to Enumerate Directly

I first came across the enumeration problem when I was writing my master's
thesis: I needed to prove (in Agda) that there were finitely many binary trees
of a given size, and that I could list them (this proof was part of a larger
verified solver for the countdown problem).
My first few attempts were unsuccessful: the algorithm presented in the
countdown paper [@hutton_countdown_2002] was not structurally recursive, and did
not seem amenable to Agda-style proofs.

Instead, I looked for a type which was isomorphic to binary trees, and which
might be easier to reason about.
One such type is Dyck words.

# Dyck Words

A "Dyck word" is a string of balanced parentheses.

```
()()
(()())()
(())()
```

It's (apparently) well-known that these strings are isomorphic to binary trees
(although the imperative descriptions of algorithms which actually computed this
isomorphism addled my brain), but what made them interesting for me was that
they are a *flat* type, structured like a linked list, and as such should be
reasonably straightforward to prove to be finite.

Our first task, then, is to write down a type for Dyck words.
Te following is a first possibility:

```haskell
data Paren = LParen | RParen
type Dyck = [Paren]
```

But this type isn't correct.
It includes many values which *don't* represent balanced parentheses, i.e. the
expressions `[LParen,RParen] :: Dyck` are well-typed.
To describe dyck words properly we'll need to reach for the GADTs:

```haskell
data DyckSuff (n :: Nat) :: Type where
  Done :: DyckSuff Z
  Open :: DyckSuff (S n) -> DyckSuff n
  Clos :: DyckSuff n     -> DyckSuff (S n)

type Dyck = DyckSuff Z
```

The first type here represents suffixes of Dyck words; a value of type
`DyckSuff n` represents a string of parentheses which is balanced except for `n`
extraneous closing parentheses.
`DyckSuff Z`, then, has no extraneous closing parens, and as such is a proper
Dyck word.

```haskell
>>> Open $ Clos $ Open $ Clos $ Done :: Dyck
()()

>>> Clos $ Open $ Clos $ Done :: DyckSuff (S Z)
)()

>>> Open $ Open $ Clos $ Open $ Clos $ Clos $ Open $ Clos $ Done :: Dyck
(()())()

>>> Open $ Open $ Clos $ Clos $ Open $ Clos $ Done :: Dyck
(())()
```

The next task is to actually enumerate these words.
Here's an $O(n)$ algorithm which does just that:

```haskell
enumDyck :: Int -> [Dyck]
enumDyck sz = go Zy sz Done []
  where
    go, zero, left, right :: Natty n -> Int -> DyckSuff n -> [Dyck] -> [Dyck]
    
    go n m k = zero n m k . left n m k . right n m k

    zero Zy 0 k = (k:)
    zero _  _ _ = id
    
    left (Sy n) m k = go n m (Open k)
    left Zy     _ _ = id
    
    right _ 0 _ = id
    right n m k = go (Sy n) (m-1) (Clos k) 

>>> mapM_ print (enumDyck 3)
"()()()"
"(())()"
"()(())"
"(()())"
"((()))"
```

A variant of this function was what I needed in my thesis: I also needed to
prove that it produced every possible value of the type `Dyck`, which was not
too difficult.

The difficult part is still ahead, though: now we need to convert between this
type and a binary tree.

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
dyckToTree :: Dyck -> Tree
dyckToTree dy = go dy (Leaf :- Nil)
  where
    go :: DyckSuff n -> Stack Tree (S n) -> Tree
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
treeToDyck :: Tree -> Dyck
treeToDyck t = go t Done
  where
    go :: Tree -> DyckSuff n -> DyckSuff n
    go Leaf        = id
    go (xs :*: ys) = go xs . Open . go ys . Clos
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

# Folds and Whatnot

Another thing I'll mention is that all of the `exec` functions presented
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

# Direct Enumeration

It turns out that you can follow relatively straightforward rewriting steps from
the Dyck-based enumeration algorithm to get to one which avoids Dyck words
entirely:

```haskell
enumTrees :: [a] -> [Tree a]
enumTrees = fmap (foldl1 (flip (:*:))) . foldlM f []
  where
    f []         v = [[Leaf v]]
    f [t1]       v = [[Leaf v, t1]]
    f (t1:t2:st) v = (Leaf v : t1 : t2 : st) : f ((t2 :*: t1) : st) v
```

Maybe in a future post I'll go through the derivation of this algorithm.

It turns out that the Dyck-based enumeration can be applied without much
difficulty to rose trees as well:

```haskell
data Rose a = a :& Forest a
type Forest a = [Rose a]

dyckToForest :: Dyck -> Forest ()
dyckToForest dy = go dy ([] :- Nil)
  where
    go :: DyckSuff n -> Stack (Forest ()) (S n) -> Forest ()
    go (Open d) ts               = go d ([] :- ts)
    go (Clos d) (t1 :- t2 :- ts) = go d ((() :& t2 : t1) :- ts)
    go Done     (t  :- Nil)      = t

forestToDyck :: Forest () -> Dyck
forestToDyck t = go t Done
  where
    go :: Forest () -> DyckSuff n -> DyckSuff n
    go []          = id
    go ((() :& x):xs) = go x . Open . go xs . Clos
```

And again, following relatively mechanical derivations, we arrive at an elegant algorithm:

```haskell
enumForests :: [a] -> [Forest a]
enumForests = foldrM f []
  where
    f x xs = zipWith ((:) . (:&) x) (inits xs) (tails xs)
```

# Related Work

While researching this post I found that enumeration of trees has been studied
*extensively* elsewhere: see @knuth_art_2006, for example, or the excellent blog
post by @tychonievich_enumerating_2013, or the entire field of [Boltzmann
sampling](https://en.wikipedia.org/wiki/Boltzmann_sampler).
This post has only scratched the surface of all of that: I hope to write much
more on the topic in the future.


# Code

As I mentioned, the Agda code for this stuff can be found
[here](https://github.com/oisdk/agda-playground/blob/d7234c276f063dbb4a2d2cbcedb86dd48501a908/Data/Dyck/Payload.agda),
I have also put all of the Haskell code in one place
[here](https://gist.github.com/oisdk/438b6e790481c908d9460ffb1196a759).

# References
