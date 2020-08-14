---
title: Some More List Algorithms
tags: Haskell
---

It's been a while since I last wrote a post (I've been busy with my Master's
thesis, which is nearly done), so I thought I would quickly throw out some fun
snippets of Haskell I had reason to write over the past couple of weeks.

# Zipping With Folds

For some reason, until recently I had been under the impression that it was
impossible to fuse zips efficiently.
In other words, I thought that `zip` was like `tail`, in that if it was
implemented using only `foldr` it would result in an asymptotic slowdown (`tail`
is normally $\mathcal{O}(1)$, implemented as a fold it's $\mathcal{O}(n)$).

Well, it seems like this is not the case.
The old zip-folding code I had looks to me now to be the correct complexity:
it's related to [How To Zip Folds](http://okmij.org/ftp/Streams.html#zip-folds),
by Oleg Kiselyov (although I'm using a different version of the function which
can be found [on the mailing
list](https://mail.haskell.org/pipermail/haskell/2005-October/016693.html)).
The relevant code is as follows:

```haskell
newtype Zip a b = 
  Zip { runZip :: a -> (Zip a b -> b) -> b }

zip :: [a] -> [b] -> [(a,b)]
zip xs ys = foldr xf xb xs (Zip (foldr yf yb ys))
  where
    xf x xk yk = runZip yk x xk
    xb _ = []
    
    yf y yk x xk = (x,y) : xk (Zip yk)
    yb _ _ = []
```

There are apparently
[reasons](https://hackage.haskell.org/package/base-4.14.0.0/docs/src/GHC.List.html#zip)
for why the Prelude's `zip` isn't allowed to fuse both of its arguments: I don't
fully understand them, however.
(in particular the linked page says that the fused zip would have different
strictness behaviour, but the version I have above seems to function properly).

This version of zip leads to some more fun solutions to folding puzzles, like
[this
one](https://old.reddit.com/r/haskell/comments/f3z18s/zipping_from_the_end_of_a_list/):

> Write a function that is equivalent to:
> ```haskell
> zipFromEnd xs ys = reverse (zip (reverse xs) (reverse ys))
> ```
> Without creating any intermediate lists.

The desired function is interesting in that, instead of lining up lists
according to their first elements, it aligns them according to the *ends*.

```haskell
>>> zipFromEnd [1,2,3] "abc"
[(1,'a'),(2,'b'),(3,'c')]

>>> zipFromEnd [1,2,3] "abcd"
[(1,'b'),(2,'c'),(3,'d')]

>>> zipFromEnd [1,2,3,4] "abc"
[(2,'a'),(3,'b'),(4,'c')]
```

The solution here is just to use `foldl`, and we get the following:

```haskell
zipFromEnd :: [a] -> [b] -> [(a,b)]
zipFromEnd xs ys = foldl xf xb xs (Zip (foldl yf yb ys)) []
  where
    xf xk x yk = runZip yk x xk
    xb _ zs = zs
    
    yf yk y x xk zs = xk (Zip yk) ((x,y) : zs)
    yb _ _ zs = zs
```

Another function which is a little interesting is the "zip longest" function:

```haskell
zipLongest :: (a -> a -> a) -> [a] -> [a] -> [a]
zipLongest c xs ys = foldr xf xb xs (Zip (foldr yf yb ys))
  where
    xf x xk yk = runZip yk (Just x) xk
    xb zs = runZip zs Nothing xb
    
    yf y yk Nothing  xk =     y : xk (Zip yk)
    yf y yk (Just x) xk = c x y : xk (Zip yk)
    
    yb Nothing  _  = []
    yb (Just x) zs = x : zs (Zip yb)
```

Finally, all of these functions rely on the `Zip` type, which is *not* strictly
positive.
This means that we can't use it in Agda, and it's tricky to reason about: I
wonder what it is about functions for deforestation that tends to lead to
non-strictly-positive datatypes.



# Lexicographic Permutations

The next puzzle I was interested in was finding the next lexicographic
permutation of some string.
In other words, given some string $s$, you need to find another string $t$ that
is a permutation of $s$ such that $s < t$, and that there is no string $u$ that
is a permutation of $s$ and $s < u < t$.
The [Wikipedia article on the
topic](https://en.wikipedia.org/wiki/Permutation#Generation_in_lexicographic_order)
is excellent (and clear), but again the algorithm is described in extremely
imperative terms:

> #. Find the largest index k such that a[k] < a[k + 1]. If no such index
>    exists, the permutation is the last permutation.
> #. Find the largest index l greater than k such that a[k] < a[l].
> #. Swap the value of a[k] with that of a[l].
> #. Reverse the sequence from a[k + 1] up to and including the final element
>    a[n].

The challenge here is to write this algorithm without doing any indexing:
indexing is expensive on Haskell lists, and regardless it is cleaner to express
it without.

I managed to work out the following:

```haskell
nextLexPerm :: Ord a => [a] -> Maybe [a]
nextLexPerm []     = Nothing
nextLexPerm (x:xs) = go1 x xs
  where
    go1 _ []     = Nothing
    go1 i (j:xs) = maybe (go2 i j [] xs) (Just . (i:)) (go1 j xs)

    go2 i j xs ys
      | j <= i    = Nothing
      | otherwise = Just (fromMaybe (j : foldl (flip (:)) (i:xs) ys) (go3 i (j:xs) ys))

    go3 _ _  []     = Nothing
    go3 i xs (j:ys) = go2 i j xs ys
```


# Circular Sorting

This comes from the [Rosetta Code problem Circle
Sort](http://rosettacode.org/wiki/Sorting_Algorithms/Circle_Sort).
This is a strange little sorting algorithm, where basically you compare elements
on opposite sides of an array, swapping them as needed.
The example given is the following:

```
6 7 8 9 2 5 3 4 1
```

First we compare (and swap) `6` and `1`, and then `7` and `4`, and so on, until
we reach the middle.
At this point we split the array in two and perform the procedure on each half.
After doing this once it is not the case that the array is definitely sorted:
you may have to repeat the procedure several (but finitely many) times, until no
swaps are performed.

I have absolutely no idea what the practical application for such an odd
algorithm would be, but it seemed like an interesting challenge to try implement
it in a functional style (i.e. without indices or mutation).

The first thing we have to do is fold the list in half, so we pair up the right
items.
We've actually seen an algorithm to do this
[before](2019-05-08-list-manipulation-tricks.html): it's often called the
"tortoise and the hare", and our previous use was to check if a list was a
palindrome.
Here's how we implement it:

```haskell
halve :: [a] -> [(a,a)]
halve xs = snd (go xs xs)
  where
    go (y:ys) (_:_:zs) = f y (go ys zs)
    go (_:ys) [_]      = (ys,[])
    go ys     []       = (ys,[])
    
    f x (y:ys,zs) = (ys, (x,y) : zs)
    
>>> halve [6,7,8,9,2,5,3,4,1]
[(6,1),(7,4),(8,3),(9,5)]
```

Notice that the `2` in the very middle of the list is missing from the output:
I'll describe how to handle that element later on.
In the above piece of code, that `2` actually gets bound to the underscore (in
`(_:ys)`) in the second clause of `go`.

Next we need to do the actual swapping: this is actually pretty straightforward,
if we think of the algorithm functionally, rather than imperatively.
Instead of swapping things in place, we are building up both halves of the new
list, so the "swap" operation should simply decide which list each item goes
into.

```haskell
halve :: Ord a => [a] -> ([a],[a])
halve xs = tl (go xs xs)
  where
    tl (_,lte,gt) = (lte,gt)
    
    go (y:ys) (_:_:zs) = swap y (go ys zs)
    go (_:ys) [_]      = (ys,[],[])
    go ys     []       = (ys,[],[])
    
    swap x (y:ys,lte,gt) 
      | x <= y    = (ys, x : lte, y : gt)
      | otherwise = (ys, y : lte, x : gt)
```

At this point we can also see what to do with the middle item: we'll put it in
the higher or lower list, depending on a comparison with the element it's next
to.

```haskell
halve :: Ord a => [a] -> ([a],[a])
halve xs = tl (go xs xs)
  where
    tl (_,lte,gt) = (lte,gt)
    
    go (y:ys) (_:_:zs) = swap y (go ys zs)
    go ys     []       = (ys,[],[])
    go (y:ys) [_]      = (ys,[y | e],[y | not e])
      where e = y <= head ys
    
    swap x (y:ys,lte,gt) 
      | x <= y    = (ys, x : lte, y : gt)
      | otherwise = (ys, y : lte, x : gt)
```

Next, we can use this as a helper function in the overall recursive function.

```haskell
circleSort :: Ord a => [a] -> [a]
circleSort [] = []
circleSort [x] = [x]
circleSort xs =
  let (lte,gt) = halve xs
  in circleSort lte ++ circleSort (reverse gt)
```

This function isn't correct (yet).
As we mentioned already, we need to run the circle sort procedure multiple times
until no swaps occur.
We can add in the tracking of swaps like so:

```haskell
circleSort :: Ord a => [a] -> [a]
circleSort xs = if swapped then circleSort ks else ks
  where
    (swapped,ks) = go xs
    
    go []  = (False, [])
    go [x] = (False, [x])
    go xs  =
      let (s,_,lte,gt) = halve xs xs
          (sl,lte') = go lte
          (sg,gt' ) = go (reverse gt)
      in (s || sl || sg, lte' ++ gt')
      
    halve (y:ys) (_:_:zs) = swap y (halve ys zs)
    halve ys     []       = (False,ys,[],[])
    halve (y:ys) [_]      = (False,ys,[y | e],[y | not e])
      where e = y <= head ys
      
    swap x (s,y:ys,lte,gt) 
      | x <= y    = (s   ,ys, x : lte, y : gt)
      | otherwise = (True,ys, y : lte, x : gt)
```

So at this point we actually have a working implementation of the function,
which avoids indices as intended.
It has some problems still, though.
First, we call `++`, when we could be using difference lists.
Here's the solution to that:

```haskell
circleSort :: Ord a => [a] -> [a]
circleSort xs = if swapped then circleSort ks else ks
  where
    (swapped,ks) = go xs []
    
    go []  zs = (False, zs)
    go [x] zs = (False, x:zs)
    go xs  zs =
      let (s,_,lte,gt) = halve xs xs
          (sl,lte') = go lte gt'
          (sg,gt' ) = go (reverse gt) zs
      in (s || sl || sg, lte')
      
    halve (y:ys) (_:_:zs) = swap y (halve ys zs)
    halve ys     []       = (False,ys,[],[])
    halve (y:ys) [_]      = (False,ys,[y | e],[y | not e])
      where e = y <= head ys
      
    swap x (s,y:ys,lte,gt) 
      | x <= y    = (s   ,ys, x : lte, y : gt)
      | otherwise = (True,ys, y : lte, x : gt)
```

Next we can actually rewrite the `go` function to allow for a certain amount of
tail recursion (kind of):

```haskell
circleSort :: Ord a => [a] -> [a]
circleSort xs = if swapped then circleSort ks else ks
  where
    (swapped,ks) = go xs (False,[])
    
    go []  (s,ks) = (s,ks)
    go [x] (s,ks) = (s,x:ks)
    go xs  (s,ks) =
      let (s',_,ls,rs) = halve s xs xs
      in go ls (go (reverse rs) (s',ks))
 
    halve s (y:ys) (_:_:zs) = swap y (halve s ys zs)
    halve s ys     []       = (s,ys,[],[])
    halve s (y:ys) [_]      = (s,ys,[y | e],[y | not e])
      where e = y <= head ys
 
    swap x (s,y:ys,ls,rs)
      | x <= y    = (   s,ys,x:ls,y:rs)
      | otherwise = (True,ys,y:ls,x:rs)
```

Next, we call `reverse`: but we can avoid the reverse by passing a parameter
which tells us which direction we're walking down the list.
Since the swapping logic is symmetric, we're able to just invert some of the
functions.
It is a little tricky, though:

```haskell
circleSort :: Ord a => [a] -> [a]
circleSort xs = if swapped then circleSort ks else ks
  where
    (swapped,ks) = go False xs (False,[])
    
    go d []  (s,ks) = sks
    go d [x] (s,ks) = (s,x:ks)
    go d xs  (s,ks) =
      let (s',_,ls,rs) = halve d s xs xs
      in go False ls (go True rs (s',ks))
 
    halve d s (y:ys) (_:_:zs) = swap d y (halve d s ys zs)
    halve d s ys     []       = (s,ys,[],[])
    halve d s (y:ys) [_]      = (s,ys,[y | e],[y | not e])
      where e = y <= head ys
 
    swap d x (s,y:ys,ls,rs)
      | bool (<=) (<) d x y = (    d || s,ys,x:ls,y:rs)
      | otherwise           = (not d || s,ys,y:ls,x:rs)
```

So there it is! 
The one-pass, purely function implementation of circle sort.
Very possibly the most useless piece of code I've ever written.
