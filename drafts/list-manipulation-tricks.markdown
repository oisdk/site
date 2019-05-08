---
title: Some Tricks for List Manipulation
tags: Haskell
bibliography: Lists.bib
---

This post is a collection of some of the tricks I've learned for efficiently
manipulating lists in Haskell.
Each one starts with a puzzle: you should try the puzzle yourself before seeing
the solution!

# The Tortoise and the Hare

> How can you split a list in half, in one pass, without taking its length?

This first one is a relatively well-known trick, but it occasionally comes in
handy, so I thought I'd mention it first.
The naive way is as follows:

```haskell
splitHalf xs = splitAt (length xs `div` 2) xs
```

But it's unsatisfying: we have to traverse the list twice, and we're taking its
length (which is almost always a bad idea).
Instead, we use the following function:

```haskell
splitHalf :: [a] -> ([a],[a])
splitHalf xs = go xs xs
  where
    go (y:ys) (_:_:zs) = first (y:) (go ys zs)
    go ys _ = ([],ys)
```

The "tortoise and the hare" is the two arguments to `go`: it traverses the
second one twice as fast, so when it hits the end, we know that the first list
must be halfway done.

# There and Back Again

> Given two lists, `xs` and `ys`, write a function which zips `xs` with the
> *reverse* of `ys` (in one pass).

There's a lovely paper [@danvy_there_2005] which goes though a number of tricks
for how to do certain list manipulations "in reverse".
Their technique is known as "there and back again".
However, I'd like to describe a different way to get to the same technique,
using folds.

Whenever I need to do some list manipulation in reverse (i.e., I need the input
list to be reversed), I first see if I can rewrite the function as a fold, and
then just switch out `foldr` for `foldl`.

For our puzzle here, we need to first write `zip` as a fold (we're going to
pretend the input lists always have the same length for now):

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip = foldr f b
  where
    f x k (y:ys) = (x,y) : k ys
    f x k [] = []
    b _ = []
```

If that looks complex, or difficult to write, don't worry!
There's a systematic way to get to the above definition from the normal version
of `zip`. 
First, let's start with a normal `zip`:

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip [] ys = []
zip xs [] = []
zip (x:xs) (y:ys) = (x,y) : zip xs ys
```

Then, we need to turn it into a case-tree, where the first branch is on the
list we want to fold over.
In other words, we want the function to look like this:

```haskell
zip xs = case xs of
  ???
```

To figure out the cases, we factor out the cases in the original function. 
Since the second clause (`zip xs [] = []`) is only reachable when `xs /= []`,
it's effectively  a case for the `x:xs` branch.


```haskell
zip :: [a] -> [b] -> [(a,b)]
zip xs = case xs of
    [] -> \_ -> []
    x:xs -> \case
        [] -> []
        y:ys -> (x,y) : zip xs ys
```

Now, we rewrite the different cases to be auxiliary functions:

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip xs = case xs of
    [] -> b
    x:xs -> f x xs
  where
    b = \_ -> []
    f = \x xs -> \case
        [] -> []
        y:ys -> (x,y) : zip xs ys
```

And finally, we *refactor* the recursive call to the first case expression.

```haskell
zip :: [a] -> [b] -> [(a,b)]
zip xs = case xs of
    [] -> b
    x:xs -> f x (zip xs)
  where
    b = \_ -> []
    f = \x xs -> \case
        [] -> []
        y:ys -> (x,y) : xs ys
```

Then those two auxiliary functions are what you pass to `foldr`!

So, to reverse it, we simply take wherever we wrote `foldr f b`, and replace it
with `foldl (flip f) b`:

```haskell
zipRev :: [a] -> [b] -> [(a,b)]
zipRev = foldl (flip f) b
  where
    f x k (y:ys) = (x,y) : k ys
    f x k [] = []
    b _ = []
```

Of course, we're reversing the wrong list here.
Fixing that is simple:

```haskell
zipRev :: [a] -> [b] -> [(a,b)]
zipRev = flip (foldl (flip f) b)
  where
    f y k (x:xs) = (x,y) : k xs
    f y k [] = []
    b _ = []
```

# Manual Fusion

> Detect that a list is a palindrome, in one pass.

We now know a good way to split a list in two, and a good way to zip a list with
its reverse.
We can *combine* the two to get a program that checks if a list is a palindrome.
Here's a first attempt:

```haskell
isPal xs = all (uncurry (==)) (uncurry zipRev (splitHalf xs))
```

But this is doing *three* passes!

To get around it, we can manually do some fusion.
Fusion is a technique where we can spot scenarios like the following:

```haskell
foldr f b (x : y : [])
```

And translate them into a version without a list:

```haskell
x `f` (y `f` b)
```

The trick is making sure that the consumer is written as a fold, and then we
just put its `f` and `b` in place of the `:` and `[]` in the producer.

But isn't `zipRev` (our consumer) written as a `foldl`, not `foldr`?
That's no problem!
`foldl` itself can be written as `foldr`:

```haskell
foldl f b xs = foldr (\x k xs -> k (f xs x)) id xs b
```

If we inline that definition into `zipRev`, we get the following:

```haskell
zipRev :: [a] -> [b] -> [(a,b)]
zipRev xs ys = foldr f id ys (const []) xs
  where
    f y k c = k (\case 
        [] -> []
        (x:xs) -> (x,y) : c xs)
```

And we can inline *that* definition into `splitHalf` to get the following:

```haskell
zipRevHalf :: [a] -> [(a,a)]
zipRevHalf xs = a (go xs xs)
  where
    go (y:ys) (_:_:zs) = first (f y) (go ys zs)
    go ys _ = (id,ys)
    a (xs,ys) = xs (const []) ys
    f y k c = k (\case 
      [] -> []
      (x:xs) -> (x,y) : c xs)

isPal xs = all (uncurry (==)) (zipRevHalf xs)
```

Finally, the `all (uncurry (==))` is implemented as a fold also.
So we can fuse it with the rest of the definitions:

```haskell
isPal :: Eq a => [a] -> Bool
isPal xs = a (go xs xs)
  where
    go (y:ys) (_:_:zs) = first (f y) (go ys zs)
    go (_:ys) [_] = (id,ys)
    go ys [] = (id,ys)
    a (xs,ys) = xs (const True) ys
    f y k c = k (\case 
      [] -> True
      (x:xs) -> (x == y) && c xs)
```

(adding a special case for odd-length lists)

Once we get to this point, we can start looking for places where we've done
unnecessary continuation-passing style.
CPS is kind of like multiplying by a negative: if you do it twice, you can
rewrite the function in a direct style.
This often happens when you use the `foldl` trick, as that's implemented using
CPS: if any of our logic was CPS'd, they should cancel out.

Here, `a` looks suspiciously like a church-encoded pair.
It takes a continuation (`xs`), and applies it to two arguments.
As it turns out, there are a few church-encoded pairs lying around.
If we take them out, we get the following very clean implementation:

```haskell
isPal :: Eq a => [a] -> Bool
isPal xs = fst (go xs xs) where
  go (y:ys) (_:_:zs) = f y (go ys zs)
  go (_:ys) [_]      = (True, ys)
  go ys     []       = (True, ys)
  
  f y (r, (z:zs))    = ((y == z) && r, zs)
```

You may have spotted the writer monad over `All` there.
Indeed, we can rewrite it to use the monadic bind:


```haskell
isPal :: forall a. Eq a => [a] -> Bool
isPal xs = getAll (fst (go xs xs)) where
  go (y:ys) (_:_:zs) = f y =<< go ys zs
  go (_:ys) [_]      = pure ys
  go ys     []       = pure ys
  
  f y (z:zs) = (All (y == z), zs)
```

# Eliminating Multiple Passes with Laziness

This is also a very well-known trick [@bird_using_1984], but today I'm going to
use it to write a function for constructing Braun trees.

A Braun tree is a peculiar structure.
It's a binary tree, where adjacent branches can differ in size by only 1.
When used as an array, it has $\mathcal{O}(\log n)$ lookup times.
It's enumerated like so:

```
     ┌─7
   ┌3┤
   │ └11
 ┌1┤
 │ │ ┌─9
 │ └5┤
 │   └13
0┤
 │   ┌─8
 │ ┌4┤
 │ │ └12
 └2┤
   │ ┌10
   └6┤
     └14
```

The objective is to construct a tree from a list in linear time, in the order
defined above.
@okasaki_three_1997 observed that, from the list:

```haskell
[0..14]
```

Each level in the tree is constructed from chucks of powers of two.
In other words:
```haskell
[[0],[1,2],[3,4,5,6],[7,8,9,10,11,12,13,14]]
```

From this, we can write the following function:

```haskell
rows k [] = []
rows k xs = (k , take k xs) : rows (2*k) (drop k xs)

build (k,xs) ts = zipWith3 Node xs ts1 ts2
  where
    (ts1,ts2) = splitAt k (ts ++ repeat Leaf)
    
fromList = head . foldr build [Leaf] . rows 1
```

The first place we'll look to eliminate a pass is the `build` function.
It combines two rows by splitting the second in half, and zipping it with the
first.

```haskell
>>> build (3, [x1,x2,x3]) [y1,y2,y3,y4,y5,y6]
[(x1,y1,y4),(x2,y2,y5),(x3,y3,y6)]
```

We don't need to store the length of the first list, though, as we are only
using it to split the second, and we can do *that* at the same time as the
zipping.

```haskell
zipUntil :: (a -> b -> c) -> [a] -> [b] -> ([c],[b])
zipUntil _ [] ys = ([],ys)
zipUntil f (x:xs) (y:ys) = first (f x y:) (zipUntil f xs ys)

>>> zipUntil (,) [1,2] "abc"
([(1,'a'),(2,'b')],"c")
```

Using this function in `build` looks like the following:

```haskell
build (k,xs) ts = zipWith ($) ys ts2
  where
    (ys,ts2) = zipUntil Node xs (ts ++ repeat Leaf)
```

That top-level `zipWith` is *also* unnecessary, though.
If we make the program circular, we can produce `ts2` as we consume it, making
the whole thing single-pass.

```haskell
build xs ts = ys
  where
    (ys,ts2) = zip3Node xs (ts ++ repeat Leaf) ts2
    zip3Node (x:xs) (y:ys) ~(z:zs) = first (Node x y z:) (zip3Node xs ys zs) 
    zip3Node [] ys _ = ([], ys)
```

That `zip3Node` is a good candidate for rewriting as a fold, also, making the
whole thing look like this:

```haskell
rows k [] = []
rows k xs = take k xs : rows (2*k) (drop k xs)

build xs ts = ys
  where
    (ys,zs) = foldr f b xs ts zs
    f x xs (y:ys) ~(z:zs) = first (Node x y z:) (xs ys zs) 
    b ys _ = ([],ys)
    
fromList = head . foldr build (repeat Leaf) . rows 1
```

To fuse all of those definitions, we first will need to rewrite `rows` as a
fold:

```haskell
rows xs = uncurry (:) (foldr f b xs 1 2)
  where
    b _ _ = ([],[])
    f x k 0 j = ([], uncurry (:) (f x k j (j*2)))
    f x k i j = first (x:) (k (i-1) j)
```

Once we have everything as a fold, the rest of the transformation is pretty
mechanical.
At the end of it all, we get the following linear-time function for constructing
a Braun tree from a list:

```haskell
fromList :: [a] -> Tree a
fromList xs = head (l (foldr f b xs 1 2))
  where
    b _ _ ys zs = (repeat Leaf, (repeat Leaf, ys))
    
    l k = let (xs, ys) = uncurry k ys in xs
    
    f x k 0 j ys zs           = ([], (l (f x k j (j*2)), ys))
    f x k i j ~(y:ys) ~(z:zs) = first (Node x y z:) (k (i-1) j ys zs)
```

# References
