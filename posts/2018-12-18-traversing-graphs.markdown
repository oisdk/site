---
title: Pure & Lazy Breadth-First Traversals of Graphs in Haskell
series: Breadth-First Traversals
bibliography: Graphs.bib
tags: Haskell
---

Today, I'm going to look at extending the previous breadth-first traversal
algorithms to arbitrary graphs (rather than just trees). Graphs with cycles are
notoriously cumbersome in functional languages, so this actually proves to be a
little trickier than I thought it would be. First, a quick recap.

# 3 Ways to Breadth-First Search

So far, we have three major ways to traverse a tree in breadth-first order. The
first is the simplest, and the fastest:

```haskell
bfe :: Tree a -> [a]
bfe r = f r b []
  where
    f (Node x xs) fw bw = x : fw (xs : bw)
  
    b [] = []
    b qs = foldl (foldr f) b qs []
```

Given a tree like the following:

```
   ┌4
 ┌2┤
 │ │ ┌8
 │ └5┤
 │   └9
1┤
 │   ┌10
 │ ┌6┘
 └3┤
   └7
```

We get:

```haskell
>>> bfe tree
[1,2,3,4,5,6,7,8,9,10]
```


It also demonstrates a theme that will run through this post: lists are the only
*visible* data structure (other than the tree, of course). However, we are
carefully batching the operations on those lists (the `foldl` is effectively a
reverse) so that they have the same complexity as if we had used a queue. In
actual fact, when lists are used this way, they *are* queues: "corecursive"
ones [@allison_circular_2006; @smith_lloyd_2009].

The next two functions perform a breadth-first traversal "level-wise": instead
of just returning all the nodes of the tree, we get them delimited by how far
they are from the root.

```haskell
lwe :: Tree a -> [[a]]
lwe r = f b r [] []
  where
    f k (Node x xs) ls qs = k (x : ls) (xs : qs)

    b _ [] = []
    b k qs = k : foldl (foldl f) b qs [] []

>>> lwe tree
[[1],[2,3],[4,5,6,7],[8,9,10]]
```

The above function is very clearly related to the `bfe` function: we just add
another queue (representing the current level), and work from there.

The third of these functions also does level-wise enumeration, but in a direct
style (without continuations).

```haskell
lwe :: Tree a -> [[a]]
lwe r = f r []
  where
    f (Node x xs) (q:qs) = (x:q) : foldr f qs xs
    f (Node x xs) []     = [x]   : foldr f [] xs
```

There are more techniques out there than just these three (including the one in
[Data.Tree](http://hackage.haskell.org/package/containers-0.6.0.1/docs/Data-Tree.html#v:levels)),
but these are my favorite, and they're what I'll be looking at today.

# Graphs and Purity

Functional programming in general excels at working with trees and similar data
structures. Graphs, though, are trickier. There's been a lot of recent work in
improving the situation [@mokhov_algebraic_2017], but I'm going to keep it
simple today: a graph is just a function.

```haskell
type Graph a = a -> [a]
```

So the tree from above could be represented as:

```haskell
graph 1 = [2,3]
graph 2 = [4,5]
graph 3 = [6,7]
graph 5 = [8,9]
graph 6 = [10]
graph _ = []
```

As it happens, all of the algorithms that follow will work on graphs represented
as rose trees (or represented any way, really).

So let's fire up our first traversal!

```haskell
bfs :: Graph a -> Graph a
bfs g r = f r b []
  where
    f x fw bw = x : fw (g x : bw)
  
    b [] = []
    b qs = foldl (foldr f) b qs []
    
>>> bfs graph 1
[1,2,3,4,5,6,7,8,9,10]
```

Unfortunately, this won't handle cycles properly:

```haskell
graph 1 = [2,3]
graph 2 = [4,5,1]
graph 3 = [6,7]
graph 5 = [8,9]
graph 6 = [10]
graph _ = []

>>> bfs graph 1
[1,2,3,4,5,1,6,7,8,9,2,3,10,4,5,1,6,7,8,9,2,3,10,4,5,1,6,7,8,9,2,3,10,4,5...
```

We need a way to mark off what we've already seen. The following isn't good
enough, also:

```haskell
>>> nub (bfs graph 1)
[1,2,3,4,5,6,7,8,9,10...
```

It will hang without finishing the list. The solution is to mark off nodes as we
find them, with some set structure:

```haskell
bfs :: Ord a => Graph a -> Graph a
bfs g ts = f ts b [] Set.empty
  where
    f x fw bw s
      | Set.member x s = fw bw s
      | otherwise      = x : fw (g x : bw) (Set.insert x s)

    b [] _ = []
    b qs s = foldl (foldr f) b qs [] s

>>> bfs graph 1
[1,2,3,4,5,6,7,8,9,10]
```

The levelwise algorithm is similar:

```haskell
lws :: Ord a => Graph a -> a -> [[a]] 
lws g r = f b r [] [] Set.empty
  where
    f k x ls qs s
      | Set.member x s = k ls qs s
      | otherwise = k (x : ls) (g x : qs) (Set.insert x s)

    b _ [] _ = []
    b k qs s = k : foldl (foldl f) b qs [] [] s
```

# Tying the Knot

The other levelwise algorithm *doesn't* translate across so easily. To see why,
let's look at the version without cycle detection:

```haskell
lws :: Graph a -> a -> [[a]]
lws g r = f r []
  where
    f x (q:qs) = (x:q) : foldr f qs (g x)
    f x []     = [x]   : foldr f [] (g x)
```

The recursive call is being made *depth*-first, not breadth-first. The result,
of course, is breadth-first, but that's only because the recursive call zips as
it goes.

Just looking at the fourth line for now:

```haskell
f x (q:qs) = (x:q) : foldr f qs (g x)
```

We want whatever process built up that `q` to be denied access to `x`. The
following doesn't work:

```haskell
f x (q:qs) = (x:filter (x/=) q) : foldr f qs (g x)
```

As well as being terribly slow, the later computation can diverge when it finds
a cycle, and filtering won't do anything to help that.

The solution is to "tie the knot". We basically do two passes over the data: one
to build up the "seen so far" list, and then another to do the actual search.
The trick is to do both of these passes at once, and feed the result back into
the demanding computation. 

```haskell
lws g r = takeWhile (not.null) (map fst (fix (f r . push)))
  where
    push xs = ([],Set.empty) : [ ([],seen) | (_,seen) <- xs ]
    f x q@((l,s):qs)
      | Set.member x s = q
      | otherwise = (x:l, Set.insert x s) : foldr f qs (g x)
```

And it works!

I got the idea for this trick from the appendix of
@okasaki_breadth-first_2000. There's something similar in
@kiselyov_pure-functional_2002.

-------
 
# References
