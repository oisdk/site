---
title: Shuffling By Sorting
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

# Permutations in Agda
## Insertion Sort
## Selection Sort
-- duality of sorts
# Improved Efficiency
## Merge Sort
## Quick Sort

