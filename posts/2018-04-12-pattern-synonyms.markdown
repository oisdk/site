---
title: 5 Cool Things You Can Do With Pattern Synonyms
tags: Haskell, Pattern Synonyms
---

[Pattern Synonyms](https://ghc.haskell.org/trac/ghc/wiki/PatternSynonyms) is an excellent extension for Haskell. There are some [very](https://ocharles.org.uk/blog/posts/2014-12-03-pattern-synonyms.html) [cool](https://www.schoolofhaskell.com/user/icelandj/Pattern%20synonyms) examples of their use out there, and I thought I'd add to the list.

# Make Things Look Like Lists

Lists are *the* fundamental data structure for functional programmers. Unfortunately, once more specialized structures are required, you often have to switch over to an uncomfortable, annoying API which isn't as pleasant or fun to use as cons and nil. With pattern synonyms, though, that's not so! For instance, here's how you would do it with a run-length-encoded list:

```haskell
data List a
    = Nil
    | ConsN {-# UNPACK #-} !Int
            a
            (List a)

cons :: Eq a => a -> List a -> List a
cons x (ConsN i y ys)
  | x == y = ConsN (i+1) y ys
cons x xs = ConsN 1 x xs

uncons :: List a -> Maybe (a, List a)
uncons Nil = Nothing
uncons (ConsN 1 x xs) = Just (x, xs)
uncons (ConsN n x xs) = Just (x, ConsN (n-1) x xs)

infixr 5 :-
pattern (:-) :: Eq a => a -> List a -> List a
pattern x :- xs <- (uncons -> Just (x, xs))
  where
    x :- xs = cons x xs
{-# COMPLETE Nil, (:-) #-}

zip :: List a -> List b -> List (a,b)
zip (x :- xs) (y :- ys) = (x,y) :- zip xs ys
zip _ _ = Nil
```

A little more useful would be to do the same with a heap:

```haskell
data Tree a
    = Leaf
    | Node a (Tree a) (Tree a)

smerge :: Ord a => Tree a -> Tree a -> Tree a
smerge Leaf ys = ys
smerge xs Leaf = xs
smerge h1@(Node x lx rx) h2@(Node y ly ry)
  | x <= y    = Node x (smerge h2 rx) lx
  | otherwise = Node y (smerge h1 ry) ly

cons :: Ord a => a -> Tree a -> Tree a
cons x = smerge (Node x Leaf Leaf)

uncons :: Ord a => Tree a -> Maybe (a, Tree a)
uncons Leaf = Nothing
uncons (Node x l r) = Just (x, smerge l r)

infixr 5 :-
pattern (:-) :: Ord a => a -> Tree a -> Tree a
pattern x :- xs <- (uncons -> Just (x, xs))
  where
    x :- xs = cons x xs
{-# COMPLETE Leaf, (:-) #-}

sort :: Ord a => [a] -> [a]
sort = go . foldr (:-) Leaf
  where
    go Leaf = []
    go (x :- xs) = x : go xs
```

In fact, this pattern can be generalized, so *any* container-like-thing with a cons-like-thing can be modified as you would with lists. You can see the generalization in [lens](https://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-Cons.html#v::-60-).

# Retroactively Make [LYAH](http://learnyouahaskell.com) Examples Work

One of the most confusing things I remember about learning Haskell early-on was that the vast majority of the Monads examples didn't work, because they were written pre-transformers. In other words, the state monad was defined like so:

```haskell
newtype State s a = State { runState :: s -> (a, s) }
```

But in transformers nowadays (which is where you get `State`{.haskell} from if you import it in the normal way), the definition is:

```haskell
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

type State s = StateT s Identity
```

This results in some *very* confusing error messages when you try run example code.

However, we can pretend that the change never happened, with a simple pattern synonym:

```haskell
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

type State s = StateT s Identity

runState :: State s a -> s -> (a, s)
runState xs = runIdentity . runStateT xs

pattern State :: (s -> (a, s)) -> State s a
pattern State x <- (runState -> x)
  where
    State x = StateT (Identity . x)
```

# Getting Type-Level Numbers With an Efficient Runtime Representation

If you want to write type-level proofs on numbers, you'll probably end up using Peano numerals and singletons:

```haskell
data Nat = Z | S Nat

data Natty n where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)

type family (+) (n :: Nat) (m :: Nat) :: Nat where
  Z + m = m
  S n + m = S (n + m)

plusZeroIsZero :: Natty n -> n + Z :~: n
plusZeroIsZero Zy = Refl
plusZeroIsZero (Sy n) = case plusZeroIsZero n of
  Refl -> Refl
```

Pretty cool, right? We can even erase the proof (if we really trust it) using rewrite rules:

```haskell
{-# RULES 
"plusZeroIsZero" forall n. plusZeroIsZero n = unsafeCoerce Refl
#-}
```

This isn't *ideal*, but it's getting there.

However, if we ever want to use these things at runtime (perhaps as a type-level indication of some data structure's size), we're going to rely on the value-level Peano addition, which is bad news.

Not so with pattern synonyms!

```haskell
data family The k :: k -> Type

class Sing (a :: k) where sing :: The k (a :: k)

data Nat = Z | S Nat

newtype instance The Nat n = NatSing Natural

instance Sing Z where
    sing = NatSing 0

instance Sing n => Sing (S n) where
    sing =
        (coerce :: (Natural -> Natural) -> (The Nat n -> The Nat (S n)))
            succ sing

data Natty n where
        ZZy :: Natty Z
        SSy :: The Nat n -> Natty (S n)

getNatty :: The Nat n -> Natty n
getNatty (NatSing n :: The Nat n) = case n of
  0 -> gcastWith (unsafeCoerce Refl :: n :~: Z) ZZy
  _ -> gcastWith (unsafeCoerce Refl :: n :~: S m) (SSy (NatSing (pred n)))

pattern Zy :: () => (n ~ Z) => The Nat n
pattern Zy <- (getNatty -> ZZy) where Zy = NatSing 0

pattern Sy :: () => (n ~ S m) => The Nat m -> The Nat n
pattern Sy x <- (getNatty -> SSy x) where Sy (NatSing x) = NatSing (succ x)
{-# COMPLETE Zy, Sy #-}

type family (+) (n :: Nat) (m :: Nat) :: Nat where
        Z + m = m
        S n + m = S (n + m)

-- | Efficient addition, with type-level proof.
add :: The Nat n -> The Nat m -> The Nat (n + m)
add = (coerce :: (Natural -> Natural -> Natural)
              -> The Nat n -> The Nat m -> The Nat (n + m)) (+)

-- | Proof on efficient representation.
addZeroRight :: The Nat n -> n + Z :~: n
addZeroRight Zy = Refl
addZeroRight (Sy n) = gcastWith (addZeroRight n) Refl
```

(unfortunately, incomplete pattern warnings don't work here)

# Hide Your Implementations

So you've got a tree type:

```haskell
data Tree a
    = Tip
    | Bin a (Tree a) (Tree a)
```

And you've spent some time writing a (reasonably difficult) function on the tree:

<details>
<summary>
Complicated function on the tree
</summary>
```haskell
showTree :: Show a => Tree a -> String
showTree Tip = ""
showTree (Bin x' ls' rs') = go True id xlen' ls'
                          $ showString xshw'
                          $ endc ls' rs'
                          $ showChar '\n'
                          $ go False id xlen' rs' ""
  where
    xshw' = show x'
    xlen' = length xshw'

    go _ _ _ Tip = id
    go up k i (Bin x ls rs) = branch True ls
                            . k
                            . pad i
                            . showChar (bool '└' '┌' up)
                            . showString xshw
                            . endc ls rs
                            . showChar '\n'
                            . branch False rs
      where
        xshw = show x
        xlen = length xshw
        branch d
          | d == up = go d (k . pad i) (xlen + 1) 
          | otherwise = go d (k . pad i . showChar '│') xlen 

    endc Tip    Tip    = id
    endc Bin {} Tip    = showChar '┘'
    endc Tip    Bin {} = showChar '┐'
    endc Bin {} Bin {} = showChar '┤'

    pad = (++) . flip replicate ' '
```
</details>

But, for some reason or another, you need to add a field to your `Bin`{.haskell} constructor, to store the size of the subtree (for instance). Does this function have to change? No! Simply change the tree definition as so:

```haskell
data Tree a
    = Tip
    | Bin' Int a (Tree a) (Tree a)

pattern Bin x ls rs <- Bin' n x ls rs
{-# COMPLETE Tip, Bin #-}
```

And all the old code works!

This gets to the core of pattern synonyms: it's another tool which we can use to separate implementation from API. 

# Better Smart Constructors

Say you've got a data type that has certain constraints on what values it can hold. You're not writing a paper for ICFP, so expressing those constraints as a beautiful type isn't required: you just want to only export the constructor and accessors, and write some tests to make sure that those functions always obey the constraints.

But once you do this you've lost something: pattern-matching. Let's get it back with pattern synonyms!

As our simple example, our constraint is going to be "A list where the values are always ordered":

```haskell
newtype List a = List { getList :: [a] }

cons :: Ord a => a -> List a -> List a
cons x (List xs) = List (insert x xs)

infixr 5 :-
pattern (:-) :: Ord a => a -> List a -> List a
pattern x :- xs <- (List (x:xs))
  where
    x :- xs = cons x xs

pattern Nil = List []
{-# COMPLETE Nil, (:-) #-}

```
