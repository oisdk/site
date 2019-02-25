---
title: Sorting Cyclic Permutations
tags: Haskell
series: Sorting
bibliography: Sorting.bib
header-includes:
  - \usepackage{asmmath}
---

There's an interesting paper on arXiv: @brown_building_2014. It describes an algorithm for building $kd$-trees. The algorithm itself is interesting enough, but what really caught my eye is the first step: sorting the cycles of tuples.

Say you have a list of three-tuples:

<style>
table{
  margin-left:auto;
  margin-right:auto;
}
</style>

|           |
|:---------:|
|  (a,b,c)  |
|  (d,e,f)  |
|  (g,h,i)  |

The cycles of those tuples are as follow:

| 1         | 2         | 3         |
|:---------:|:---------:|:---------:|
|  (a,b,c)  |  (b,c,a)  |  (c,a,b)  |
|  (d,e,f)  |  (e,f,d)  |  (f,d,e)  |
|  (g,h,i)  |  (h,i,g)  |  (i,g,h)  |

Now, the task is to sort each of those lists (1, 2, and 3), and return the list of original positions. "Returning the original positions" here means taking a list, pairing each item with its index, sorting the items, and spitting back out the indices. Let's try with an example: take the string "cat":

```haskell
"cat"
```

Pair each item with its index:

```haskell
[(0,'c'),(1,'a'),(2,'t')]
```

Sort the items:

```haskell
[(1,'a'),(0,'c'),(2,'t')]
```

And spit back out the indices:

```haskell
[1,0,2]
```

As a torture-test, we can use the example from the paper:

|    |   Input   |  Output    |
|---:|:---------:|:----------:|
|  0 |  (2,3,3)  | (11,13,9)  |
|  1 |  (5,4,2)  | (13,4,6)   |
|  2 |  (9,6,7)  | (0,5,1)    |
|  3 |  (4,7,9)  | (10,9,7)   |
|  4 |  (8,1,5)  | (3,0,13)   |
|  5 |  (7,2,6)  | (1,6,0)    |
|  6 |  (9,4,1)  | (9,1,12)   |
|  7 |  (8,4,2)  | (5,7,10)   |
|  8 |  (9,7,8)  | (4,10,4)   |
|  9 |  (6,3,1)  | (7,12,5)   |
| 10 |  (3,4,5)  | (14,2,14)  |
| 12 |  (1,6,8)  | (6,11,2)   |
| 13 |  (9,5,3)  | (12,14,11) |
| 14 |  (2,1,3)  | (2,8,8)    |
| 15 |  (8,7,6)  | (8,3,3)    |

