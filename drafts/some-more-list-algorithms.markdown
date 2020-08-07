---
title: Some More List Algorithms
tags: Haskell
---

It's been a while since I last wrote a post (I've been busy with my Master's
thesis, which is nearly done), so I thought I would quickly throw out some fun
snippets of Haskell I had reason to write over the past couple of weeks.

The first comes from the [Rosetta Code problem Circle
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
