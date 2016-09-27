---
title: A Trie in Haskell
tags: Haskell
description: A basic Trie in Haskell
---

## Basic Ops

A Trie is one of those data structures that I find myself writing very early on in almost every language I try to learn. It's elegant and interesting, and easy enough to implement.

I usually write a version that is a set-like data structure, rather than a mapping type, for simplicity's sake. It stores sequences, in a prefix-tree structure. It has a map (dictionary) where the keys are the first element of every sequence it stores, and the values are the Tries which store the rest of the sequence. It also has a boolean tag, representing whether or not the current Trie is a Trie on which a sequence ends. Here's what the type looks like in Haskell:

```{.haskell .literate .hidden_source}
module Trie where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Prelude hiding (null)
import Data.Maybe
import Control.Monad
import Data.Foldable (fold)
```
```{.haskell .literate}
data Trie a = Trie { endHere :: Bool
                   , getTrie :: Map a (Trie a)
                   } deriving (Eq)
```

Now, inserting into the Trie is easy. You just `uncons`{.haskell} on a list, and insert the head into the map, with the value being the tail inserted into whatever existed at that key before:

```{.haskell .literate}
empty :: Trie a
empty = Trie False Map.empty

insertRec :: Ord a => [a] -> Trie a -> Trie a
insertRec [] (Trie _ m)     = Trie True m
insertRec (x:xs) (Trie e m) = 
  Trie e (Map.alter (Just . insertRec xs . fromMaybe empty) x m)
```
    
Searching is simple, also. For the empty list, you just check if the Trie has its `endHere`{.haskell} tag set to `True`{.haskell}, otherwise, you uncons, search the map, and query the Trie with the tail if it eas found, or just return `False`{.haskell} if it was not:

```{.haskell .literate}
memberRec :: Ord a => [a] -> Trie a -> Bool
memberRec [] (Trie e _)     = e
memberRec (x:xs) (Trie _ m) = 
  fromMaybe False (memberRec xs <$> Map.lookup x m)
```

Here's my problem. *Both* of those functions have the same pattern:

```haskell
f []     = ...
f (x:xs) = ...
```

Any good Haskeller should be *begging* for a fold at this stage. But it proved a little trickier than I'd imagined. Take `member`{.haskell}, for instance. You want to fold over a list, with the base case being the tag on the Trie:

```haskell
member :: Ord a => [a] -> Trie a -> Bool
member = foldr f base where
  base = ???
  f e a = Map.lookup e ???
```

Where do you get the base case from, though? You have to specify it from the beginning, but the variable you're looking for is nested deeply into the Trie. How can you look into the Trie, without traversing the list, to find the tag, *at the beginning of the function?*

That had been my issue for a while. Every time I cam back to writing a Trie, I would see the pattern, try and write `insert`{.haskell} and `member`{.haskell} with a fold, and remember again the trouble I had had with it in the past. Recently, though, I saw a different problem, that gave me an idea for a solution.

## The Highest Order

> Rewrite `dropWhile`{.haskell} using `foldr`{.haskell}
 
It's a (semi) well-known puzzle, that's maybe a little more difficult than it seems at first. Here, for instance, was my first attempt at it:

```{.haskell .literate}
dropWhileWrong :: (a -> Bool) -> [a] -> [a]
dropWhileWrong p = foldr f [] where
  f e a | p e       = a
        | otherwise = e:a
```

Yeah. That's `filter`{.haskell}, not `dropWhile`{.haskell}:

```{.haskell .literate .example}
dropWhileWrong (<5) [1, 3, 6, 3, 1]
[6]
```
    
Here was my final solution:

```{.haskell .literate}
dropWhileCount :: (a -> Bool) -> [a] -> [a]
dropWhileCount p l = drop (foldr f 0 l) l where
  f e a | p e       = a + 1
        | otherwise = 0
```
            
After the problem I found [this](https://wiki.haskell.org/wikiupload/1/14/TMR-Issue6.pdf) issue of The Monad Reader, which talks about the same problem. In my `drop`{.haskell} version, I had been counting the number of items to drop as I went, adding one for every element that passed the test. The corresponding version in the article had been building up `tail`{.haskell} functions, using `.`{.haskell} to add them together:

```{.haskell .literate}
dropWhileTail :: (a -> Bool) -> [a] -> [a]
dropWhileTail p l = (foldr f id l) l where
  f e a | p e       = tail . a
        | otherwise = id
```
            
A quick visit to [pointfree.io](http://pointfree.io) can generate some monadic pointsfree magic:

```{.haskell .literate}
dropWhilePf :: (a -> Bool) -> [a] -> [a]
dropWhilePf p = join (foldr f id) where
  f e a | p e       = tail . a
        | otherwise = id
```

Now, the final version in the article did *not* use this technique, as it was very inefficient. It used some cleverness beyond the scope of this post. The second-from-last version I quite liked, though:

```{.haskell .literate}
dropWhileFp :: (a -> Bool) -> [a] -> [a]
dropWhileFp p l = foldr f l l where
  f e a | p e       = tail a
        | otherwise = l
```
            
However, the idea of building up a function in a fold gave me an idea for adapting it to some of the Trie functions.

## Folding Inwards

Let's start with `member`{.haskell}. It needs to fold over a list, and generate a function which acts on a Trie:

```haskell
member :: Ord a => [a] -> Trie a -> Bool
member = foldr f base
```

The `base`{.haskell} is the function being built up: the final part of the function chain. Each part of the function is generated based on each element of the list, and then chained with the base using `.`{.haskell}:

```haskell
member = foldr f base where
  f e a = ??? . a 
```
      
The base here is what's called when the list is empty. Here's what it looked like in the explicit recursion version:

```haskell
member [] (Trie e _) = e
```
    
We could simplify this by using record syntax, and `getTrie`{.haskell}:

```haskell
member [] t = getTrie t
```

And this has an obvious pointsfree version:

```haskell
member [] = getTrie
```
    
That fits for the base case. It's just a function:

```haskell
member = foldr f endHere where
  f e a = ??? . a 
```

Then, how to combine it. That's easy enough, actually. It accesses the map, searches it for the key, and calls the accumulating function on it. If it's not found in the map, just return `False`{.haskell}. Here it is:

```{.haskell .literate}
member :: Ord a => [a] -> Trie a -> Bool
member = foldr f endHere where
  f e a = fromMaybe False . fmap a . Map.lookup e . getTrie
```
      
One of the other standard functions for a Trie is returning the "completions" for a given sequence. It's a very similar function to `member`{.haskell}, actually: instead of calling `endHere`{.haskell} on the final Trie found, though, just return the Trie itself. And the thing to return if any given element of the sequence isn't found is just an empty Trie:

```{.haskell .literate}
complete :: Ord a => [a] -> Trie a -> Trie a
complete = foldr f id where
  f e a = fromMaybe empty . fmap a . Map.lookup e . getTrie 
```
      
In fact, you could abstract out the commonality here:

```{.haskell .literate}
follow :: Ord a => c -> (Trie a -> c) -> [a] -> Trie a -> c
follow ifMiss onEnd = foldr f onEnd where
  f e a = fromMaybe ifMiss . fmap a . Map.lookup e . getTrie 
  
memberAbs :: Ord a => [a] -> Trie a -> Bool
memberAbs = follow False endHere

completeAbs :: Ord a => [a] -> Trie a -> Trie a
completeAbs = follow empty id
```
    
## Folding in and out

`insert`{.haskell} is another deal entirely. In `member`{.haskell}, the fold was tunneling into a Trie, applying the accumulator function to successively deeper Tries, and returning a result based on the final Trie. `insert`{.haskell} needs to do the same tunneling - but the Trie returned needs to be the *outer* Trie.

It turns out it's not that difficult. Instead of "building up a function" that is then applied to a Trie, here a function is "sent" into the inner Tries. The cool thing here is that the function being sent hasn't been generated yet.

Here's some more illustration of what I mean. Start off with the normal `foldr`{.haskell}:

```haskell
insert :: Ord a => [a] -> Trie a -> Trie a
insert = foldr f (\(Trie _ m) -> Trie True m)
```

With the final function to be applied being one that just flips the `endHere`{.haskell} tag to `True`{.haskell}. Then `f`{.haskell}: this is going to act *over* the map of the Trie that it's called on. It's useful to define a function just for that:

```{.haskell .literate}
overMap :: Ord b 
        => (Map.Map a (Trie a)
        -> Map.Map b (Trie b))
        -> Trie a
        -> Trie b
overMap f (Trie e m) = Trie e (f m)
```
    
Then, it will look up the next element of the sequence in the Trie, and apply the accumulating function to it. (if it's not found it will provide an empty Trie instead) Simple!

```{.haskell .literate .hidden_source}
instance Ord a => Monoid (Trie a) where
  mempty = Trie False Map.empty
  Trie v k `mappend` Trie t l =
    Trie (v || t) (Map.unionWith mappend k l)
```

```{.haskell .literate}
insert :: Ord a => [a] -> Trie a -> Trie a
insert = foldr f (\(Trie _ m) -> Trie True m) where
  f e a = 
    overMap (Map.alter (Just . a . fold) e)
```
      
I think this is really cool: with just a `foldr`{.haskell}, you're burrowing into a Trie, changing it, and burrowing back out again.

## Removal

This is always the tricky one with a Trie. You *can* just follow a given sequence down to its tag, and flip it from on to off. But that doesn't remove the sequence itself from the Trie. So maybe you just delete the sequence - but that doesn't work either. How do you know that there are no other sequences stored below the one you were examining?

What you need to do is to send a function into the Trie, and have it report back as to whether or not it stores other sequences below it. So this version of `foldr`{.haskell} is going to burrow into the Trie, like `member`{.haskell}; maintain the outer Trie, like `insert`{.haskell}; but *also* send messages back up to the outer functions. Cool!

The way to do the "message sending" is with `Maybe`{.haskell}. If the function you send into the Trie to delete the end of the sequence returns `Nothing`{.haskell}, then it signifies that you can delete that member. Luckily, the `alter`{.haskell} function on `Data.Map`{.haskell} works well with this:

```haskell
alter :: Ord k 
      => (Maybe a -> Maybe a)
      -> k
      -> Map k a
      -> Map k a
```
    
Its first argument is a function which is given the result of looking up its *second* argument. If the function returns `Nothing`{.haskell}, that key-value pair in the map is deleted (if it was there). If it returns `Just`{.haskell} something, though, that key-value pair is added. In the delete function, we can chain the accumulating function with `=<<`{.haskell}. This will skip the rest of the accumulation if any part of the sequence isn't found. The actual function we're chaining on is `nilIfEmpty`{.haskell}, which checks if a given Trie is empty, and returns `Just`{.haskell} the Trie if it's not, or `Nothing`{.haskell} otherwise.

Here's the finished version:

```{.haskell .literate}
delete :: Ord a => [a] -> Trie a -> Trie a
delete = (fromMaybe empty .) . foldr f i where
  i (Trie _ m) | Map.null m  = Nothing
               | otherwise = Just (Trie False m)
  f e a = nilIfEmpty . overMap (Map.alter (a =<<) e) 
  
null :: Trie a -> Bool
null (Trie e m) = (not e) && (Map.null m)

nilIfEmpty :: Trie a -> Maybe (Trie a)
nilIfEmpty t | null t    = Nothing
             | otherwise = Just t
```
      
## Folding the Foldable

So how about folding the Trie itself? Same trick: build up a function with a fold. This time, a fold over the map, not a list. And the function being built up is a cons operation. When you hit a `True`{.haskell} tag, fire off an empty list to the built-up function, allowing it to evaluate:

```{.haskell .literate}
foldrTrie :: ([a] -> b -> b) -> b -> Trie a -> b
foldrTrie f i (Trie a m) = Map.foldrWithKey ff s m where
  s    = if a then f [] i else i
  ff k = flip (foldrTrie $ f . (k :))
```
      
Unfortunately, [it's not easy](http://stackoverflow.com/questions/33469157/foldable-instance-for-a-trie-set) to make the Trie *conform* to `Foldable`{.haskell}. It is possible, and it's what I'm currently trying to figure out, but it's non-trivial.
