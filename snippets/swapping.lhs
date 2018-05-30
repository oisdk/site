---
title: Swapping
---

\begin{code}
{-# LANGUAGE RecursiveDo #-}

module Swap where

import qualified Data.Map.Strict as Map
import           Data.Map.Strict   (Map)

import           Data.IntMap          (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntMap.Lazy   as LazyIntMap

import           Control.Lens

import           Control.Arrow           ((&&&))
import           Control.Monad           ((>=>))
import           Control.Monad.Fix       (mfix)

import           Control.Monad.State     (StateT(..),execState,state)

import           Data.Maybe  (fromMaybe)
import           Data.Monoid (First(..))
\end{code}

Say you want to swap two items in a mapping structure---[Data.Map.Strict](http://hackage.haskell.org/package/containers-0.5.11.0/docs/Data-Map-Strict.html), [Data.HashMap](https://hackage.haskell.org/package/unordered-containers-0.2.9.0/docs/Data-HashMap-Strict.html), etc. The normal way uses far too many operations:

\begin{code}
-- |
-- >>> swapAt4 1 2 (Map.fromList (zip [1..5] ['a'..]))
-- fromList [(1,'b'),(2,'a'),(3,'c'),(4,'d'),(5,'e')]
swapAt4 :: Ord a => a -> a -> Map a b -> Map a b
swapAt4 i j xs = case Map.lookup i xs of
  Nothing -> xs
  Just x -> case Map.lookup j xs of
    Nothing -> xs
    Just y -> Map.insert i y (Map.insert j x xs)
\end{code}

Two lookups, and two insertions. We can cut it down to three operations with [`insertLookupWithKey`](http://hackage.haskell.org/package/containers-0.5.11.0/docs/Data-Map-Strict.html#v:insertLookupWithKey):

\begin{code}
-- |
-- >>> swapAt3 1 2 (Map.fromList (zip [1..5] ['a'..]))
-- fromList [(1,'b'),(2,'a'),(3,'c'),(4,'d'),(5,'e')]
swapAt3 :: Ord a => a -> a -> Map a b -> Map a b
swapAt3 i j xs = case Map.lookup i xs of
  Nothing -> xs
  Just x -> case Map.insertLookupWithKey (const const) j x xs of
    (Nothing,_) -> xs
    (Just y,ys) -> Map.insert i y ys
\end{code}

Then, using laziness, we can write the above program [circularly](https://doi.org/10.1007/BF00264249), reducing the number of lookups to 2:

\begin{code}
swapAt2 :: Ord a => a -> a -> Map a b -> Map a b
swapAt2 i j xs = zs
  where
     (ival,ys) = Map.updateLookupWithKey (replace jval) i xs
     (jval,zs) = Map.updateLookupWithKey (replace ival) j ys
     replace x = const (Just . (`fromMaybe` x))
\end{code}

Unfortunately, Data.Map isn't lazy enough for this: the above won't terminate. Interestingly, Data.IntMap *is* lazy enough:

\begin{code}
swapAt2Int :: Int -> Int -> IntMap a -> IntMap a
swapAt2Int i j xs = zs
  where
    (ival,ys) = LazyIntMap.updateLookupWithKey (replace jval) i xs
    (jval,zs) =     IntMap.updateLookupWithKey (replace ival) j ys
    replace x = const (Just . (`fromMaybe` x))
\end{code}

Notice how we have to use the lazy version of `updateLookupWithKey`{.haskell}. Again, though, this version has a problem: it won't terminate when one of the keys is missing.

Thankfully, both of our problems can be solved by abstracting a little and using [Ixed](http://hackage.haskell.org/package/lens-4.16.1/docs/Control-Lens-At.html#t:Ixed) from lens:

\begin{code}
-- |
-- >>> swapIx 1 2 "abc"
-- "acb"
swapIx :: Ixed a => Index a -> Index a -> a -> a
swapIx i j xs = zs
  where
    (First ival, ys) = ix i (replace jval) xs
    (First jval, zs) = ix j (replace ival) ys
    replace x = First . Just &&& (`fromMaybe` x)
\end{code}

Because `ix`{.haskell} is a traversal, it won't do anything when there's a missing key, which is what we want. Also, it adds extra laziness, as the caller of a traversal gets certain extra controls over the strictness of the traversal.

You may notice the stateful pattern above. However, translating it over as-is presents a problem: the circular bindings won't work in vanilla do notation. For that, we need [`MonadFix`{.haskell}](http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Monad-Fix.html) and [Recursive Do](https://ocharles.org.uk/blog/posts/2014-12-09-recursive-do.html):

\begin{code}
swapSt :: Ixed a => Index a -> Index a -> a -> a
swapSt i j = execState $ mdo
    ival <- replace i jval
    jval <- replace j ival
    pure ()
  where
    replace i (First x) =
        state (ix i (First . Just &&& (`fromMaybe` x)))
\end{code}

Finally, we can use [`mfix`{.haskell}](http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Monad-Fix.html#v:mfix) directly, and we'll get the following clean-looking solution:

\begin{code}
swap :: Ixed a => Index a -> Index a -> a -> a
swap i j = execState (mfix (replace i >=> replace j))
  where
    replace i (First x) =
        state (ix i (First . Just &&& (`fromMaybe` x)))
\end{code}

This works for most containers, even strict ones like Data.Map.Strict. It also works for Data.Vector. It does *not* work for Data.Vector.Unboxed, though.
