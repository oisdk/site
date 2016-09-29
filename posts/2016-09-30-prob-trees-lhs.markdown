---
title: Probability Trees
tags: Haskell
bibliography: Probability.bib
---
```{.haskell .literate .hidden_source}
{-# language DeriveFunctor, DeriveFoldable #-}
{-# language PatternSynonyms, ViewPatterns #-}

module ProbTree where

import Data.Monoid
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Arrow
import Data.Ratio
import Data.Foldable
```
Previously, I tried to figure out how to make the probability monad more "listy". I read a little more about the topic [especially @erwig_functional_2006; and @kidd_build_2007].

I then thought about what a probability monad would look like if it was based on other data structures. I feel like the standard version really wants to be:

```{.haskell .literate}
newtype ProperProb a = ProperProb
  { yes :: Map a (Product Rational) }
```

But of course a monad instance isn't allowed.

Similar to a map, though, is a binary tree:

```{.haskell .literate}
data BinaryTree a = Leaf
                  | Node (BinaryTree a) a (BinaryTree a)
```

And it feels better for probability - *flatter*, somehow. Transmuting it into a probability-thing:

```{.haskell .literate}
data Odds a = Certain a
            | Choice (Odds a) Rational (Odds a)
            deriving (Eq, Functor, Foldable, Show)
```

That looks good to me. A choice between two different branches feels more natural than a choice between a head and a tail.

The fold is similar to before, with an unfold for good measure:

```{.haskell .literate}
foldOdds :: (b -> Rational -> b -> b) -> (a -> b) -> Odds a -> b
foldOdds f b = r where
  r (Certain x) = b x
  r (Choice xs p ys) = f (r xs) p (r ys)
  
unfoldOdds :: (b -> Either a (b,Rational,b)) -> b -> Odds a
unfoldOdds f = r where
  r b = case f b of
    Left a -> Certain a
    Right (x,p,y) -> Choice (r x) p (r y)
  
fi :: Bool -> a -> a -> a
fi True  t _ = t
fi False _ f = f
```

I changed the pattern synonym a little:

```{.haskell .literate}

unRatio :: Num a => Rational -> (a,a)
unRatio = numerator   &&& denominator 
      >>> fromInteger *** fromInteger

pattern n :% d <- (unRatio -> (n,d))
```

Then, the `probOf`{.haskell} function:

```{.haskell .literate}
probOf :: Eq a => a -> Odds a -> Rational
probOf e = foldOdds f b where
  b x = fi (e == x) 1 0
  f x (n:%d) y = (x * n + y * d) / (n + d)
```

This version doesn't have the option for short-circuiting on the first value it finds.

For generating from lists, you can try to evenly divide the list among each branch.

```{.haskell .literate}
fromListOdds :: (([b], Int) -> Integer) -> (b -> a) -> [b] -> Maybe (Odds a)
fromListOdds fr e = r where
  r [] = Nothing
  r xs = Just (unfoldOdds f (xs, length xs))
  f ([x],_) = Left (e x)
  f (xs ,n) = Right ((ys,l), fr (ys,l) % fr (zs,r), (zs,r)) where
    l = n `div` 2
    r = n - l
    (ys,zs) = splitAt l xs

equalOdds :: [a] -> Maybe (Odds a)
equalOdds = fromListOdds (fromIntegral . snd) id

fromDistrib :: [(a,Integer)] -> Maybe (Odds a)
fromDistrib = fromListOdds (sum . map snd . fst) fst
```

What's really nice about this version is the fact that the old `append`{.haskell} is just the `Choice`{.haskell} constructor, leaving the instances to be really nice:

```{.haskell .literate}
flatten :: Odds (Odds a) -> Odds a
flatten = foldOdds Choice id

instance Applicative Odds where
  pure = Certain
  fs <*> xs = flatten (fmap (<$> xs) fs)
  
instance Monad Odds where
  x >>= f = flatten (f <$> x)
```

Finally, as a bonus, to remove duplicates:

```{.haskell .literate}
counts :: (Ord a, Foldable f, Num n) => f a -> [(a,n)]
counts = 
  Map.assocs . 
    foldl' 
      ((flip . Map.alter) (Just . foldr (+) 1)) 
      Map.empty
      
compress :: Ord a => Odds a -> Odds a
compress xs = let Just ys = (fromDistrib . counts) xs in ys
```
After reading yet more on this, I found that the main issue with the monad is its performance. Two articles in particular: @larsen_memory_2011, and @scibior_practical_2015, refer to a GADT implementation of the monad which maximises laziness.

### References
