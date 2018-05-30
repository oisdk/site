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
import           Data.Profunctor.Unsafe  ((#.))
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

Then, using laziness, we can write the above program circularly, reducing the number of lookups to 2:

\begin{code}
swapAt2 :: Ord a => a -> a -> Map a b -> Map a b
swapAt2 i j xs = zs
  where
     (ival,ys) = Map.updateLookupWithKey (replace jval) i xs
     (jval,zs) = Map.updateLookupWithKey (replace ival) j ys
     replace x = const (Just . flip fromMaybe x)
\end{code}

But unfortunately, Data.Map doesn't have the laziness necessary to perform this. We can use, instead, Data.IntMap:

\begin{code}
swapAt2Int :: Int -> Int -> IntMap a -> IntMap a
swapAt2Int i j xs = zs
  where
    (ival,ys) = LazyIntMap.updateLookupWithKey (replace jval) i xs
    (jval,zs) =     IntMap.updateLookupWithKey (replace ival) j ys
    replace x = const (Just . flip fromMaybe x)
\end{code}

Noticing the state-like pattern, we can make it explicit:

\begin{code}
swapAt2State :: Int -> Int -> IntMap a -> IntMap a
swapAt2State i j = execState $ mdo
    ival <- state $ LazyIntMap.updateLookupWithKey (replace jval) i
    jval <- state $     IntMap.updateLookupWithKey (replace ival) j
    return ()
  where replace x = const (Just . flip fromMaybe x)
\end{code}

We can generalize even further, to use Ixed:

\begin{code}
swapAt2Ixed :: Ixed a => Index a -> Index a -> a -> a
swapAt2Ixed i j = execState $ mdo
  First ival <- state $ ix i (First . Just &&& flip fromMaybe jval)
  First jval <- state $ ix j (First . Just &&& flip fromMaybe ival)
  return ()
\end{code}

Finally, we can remove the do notation, for the full operator-soup glory:

\begin{code}
swap :: Ixed a => Index a -> Index a -> a -> a
swap i j = execState (mfix (replace i >=> replace j))
  where
    replace i = (fmap getFirst . state)
             #. ix i
              . (&&&) (First #. Just)
              . flip fromMaybe
\end{code}
