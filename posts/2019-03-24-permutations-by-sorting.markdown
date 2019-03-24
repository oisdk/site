---
title: Permutations By Sorting
tags: Haskell, Agda
bibliography: Sorting.bib
---

A naive---and wrong---way to shuffle a list is to assign each element in the
list a random number, and then sort it. 
It might not be immediately obvious why: @kiselyov_provably_2002 has a good
explanation as to the problem.
One way to think about it is like this: choosing $n$ random numbers each in the
range $[0,n)$ has $n^n$
possible outcomes, whereas there are $n!$ permutations: these don't necessarily
divide evenly into each other, so you're going to have some bias.

# Factorial Numbers

The first part of the fix is to figure out a way to get some random data that
has only $n!$ possible values.
The trick here will be to mimic the structure of a factorial itself: taking $n =
5$, the previous technique would have yielded:

$$5 \times 5 \times 5 \times 5 \times 5 = 5^5$$

possible values. But we want:

$$5 \times 4 \times 3 \times 2 \times 1 = 5!$$

The solution is simple, then! Simply decrement the range by one for each
position in the output list. In Haskell:

```haskell
nums :: Int -> IO [Int]
nums 0 = pure []
nums n = (:) <$> randomR (0,n) <*> nums (n-1)
```

As an aside, what we've done here is constructed a list of digits in the
[factorial number
system](https://en.wikipedia.org/wiki/Factorial_number_system).

# Sorts

Unfortunately, while we've figured out a way to get properly distributed random
data, we can't yet sort it to shuffle our list. If we look at the 6 factorial
numbers generated for $n = 5$, we can see the problem:

```
000
010
100
110
200
210
```

Different values in the list will produce the same sort: `100` and `200`, for
instance.

# Lehmer Codes

We need a way to map the numbers above to a particular permutations: that's
precisely the problem solved by [Lehmer
codes](https://en.wikipedia.org/wiki/Lehmer_code). 
For the numbers `110`, we can think of each digit as the relative position to
put that item from the string into.
Some Haskell code might make it clear:

```haskell
insert :: Int -> a -> [a] -> [a]
insert 0 x xs = x : xs
insert i x (y:ys) = y : insert (i-1) x ys

shuffle :: [a] -> [Int] -> [a]
shuffle xs ys = foldr (uncurry insert) [] (zip ys xs)
```

And we can step through its execution:

```haskell
shuffle "abc" [1,1,0]
foldr (uncurry insert) [] [(1,'a'),(1,'b'),(0,'c')]
insert 1 'a' (insert 1 'b' (insert 0 'c' []))
insert 1 'a' (insert 1 'b' "c")
insert 1 'a' "cb"
'c' : insert 0 'a' "b"
"cab"
```

# Dualities of Sorts

Notice the similarity of the function above to a standard insertion sort:

```haskell
insert :: Ord a => a -> [a] -> [a]
insert x [] = x : xs
insert x (y:ys)
 | x <= y = x : y : ys
 | otherwise = y : insert x ys

insertSort :: Ord a => [a] -> [a]
insertSort = foldr insert []
```

The "comparison" is a little strange---we have to take into account relative
position---but the shape is almost identical.
Once I spot something like that, my first thought is to see if the relationship
extends to a better $\mathcal{O}(n \log n)$ sort, but there's something else I'd
like to look at first.

"A Duality of Sorts" [@hinze_duality_2013] is a paper based on the interesting
symmetry between insertion sort and selection sort [There's also a
video of Graham Hutton explaining the idea; @haran_sorting_2016].

With that paper in mind, can we rewrite `shuffle` as a selection-based
algorithm? We can indeed!

```haskell
pop :: [(Int,a)] -> Maybe (a, [(Int,a)])
pop [] = Nothing
pop ((0,x):xs) = Just (x, xs)
pop ((i,x):xs) = (fmap.fmap) ((i-1,x):) (pop xs)

shuffle :: [a] -> [Int] -> [a]
shuffle xs ys = unfoldr pop (zip ys xs)
```

While the symmetry is pleasing, the paper details how to make the relationship
explicit, using the same function for both selection and insertion sort:

```haskell
swop Nil = Nil
swop (Cons a (x , Nil)) = Cons a (Left x)
swop (Cons a (x , Cons b x'))
  | fst a == 0 = Cons a (Left x)
  | otherwise  = Cons b (Right (Cons (first pred a) x'))
  
ishuffle :: [(Int,a)] -> [(Int,a)]
ishuffle = cata (apo (swop . fmap (id &&& project)))

sshuffle :: [(Int,a)] -> [(Int,a)]
sshuffle = ana (para (fmap (id ||| embed) . swop))
```

# Improved Efficiency

So now we have to upgrade our sorts: in the paper, merge sort is the more
efficient sort chosen, similarly to what I chose
[previously](2018-12-21-balancing-scans.html#random-shuffles).

```haskell
merge [] ys = ys
merge xs [] = xs
merge ((x,i):xs) ((y,j):ys)
  | i <= j    = (x,i) : merge xs ((y,j-i):ys)
  | otherwise = (y,j) : merge ((x,i-j-1):xs) ys
  
treeFold :: (a -> a -> a) -> a -> [a] -> a
treeFold f = go
  where
    go x [] = x
    go a (b:l) = go (f a b) (pairMap l)
    pairMap (x:y:rest) = f x y : pairMap rest
    pairMap xs = xs
    
shuffle xs inds = map fst $ treeFold merge [] $ map pure $ zip xs inds
```

However, I feel like merge sort is an upgrade of *insertion* sort, not selection
sort.
Indeed, if you do the "split" step of merge sort badly, i.e. by splitting very
unevenly, merge sort in fact *becomes* insertion sort!

So there's a missing bit of this table:

|                         | Insertion      | Selection      |
|-------------------------|:--------------:|:--------------:|
| $\mathcal{O}(n^2)$      | Insertion sort | Selection sort |
| $\mathcal{O}(n \log n)$ | Merge sort     | ???            |

I think it's clear that quicksort is the algorithm that fits in there: again,
done badly it degrades to selection sort (if you intentionally pick the pivot to
be the worst element possible, i.e. the smallest element).

There are more symmetries: merge sort splits the lists using their structure,
and merges them using the ordering of the elements. Quicksort is the opposite,
merging by concatenation, but splitting using order. Finally, in merge sort
adjacent elements are in the correct order after the recursive call, but the two
sides of the split are not. Again, quicksort is precisely the opposite: adjacent
elements have not been compared (*before* the recursive call), but the two sides
of the split are correctly ordered.

Anyway, I haven't yet formalised this duality (and I don't know if I can), but
we *can* use it to produce a quicksort-based shuffle algorithm:

```haskell
partition = foldr f (const ([],[]))
  where
    f (y,j) ys i
      | i <= j    = fmap  ((y,j-i):) (ys i)
      | otherwise = first ((y,j):) (ys (i-1))
      
shuffle :: [a] -> [Int] -> [a]
shuffle xs ys = go (zip xs ys)
  where
    go [] = []
    go ((x,i):xs) = case partition xs i of
        (ls,rs) -> go ls ++ [x] ++ go rs
```

That's all for this post! The algorithms can all be translated into Agda or
Idris: I'm currently working on a way to represent permutations that isn't
$\mathcal{O}(n^2)$ using them. If I figure out a way to properly dualise
quicksort and merge sort I'll do a small write up as well [I'm currently working
my way through @hinze_sorting_2012 for ideas]. Finally, I'd like to
explore some other sorting algorithms as permutation algorithms: sorting
networks seem especially related to "permutations by swapping".

# References
