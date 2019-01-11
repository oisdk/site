---
title: What is Good About Haskell?
tags: Haskell
---

Beginners to Haskell are often confused as to what's so great about the
language. Much of the proselytizing online focuses on pretty abstract (and often
poorly defined) concepts like "purity", "strong types", and (god forbid)
"monads". These things are difficult to understand, somewhat controversial, and
not obviously beneficial (especially when you've only been using the language
for a short amount of time).

The real tragedy is that Haskell (and other ML-family languages) are *packed*
with simple, decades-old features like pattern matching and algebraic data types
which have massive, clear benefits and few (if any) downsides. Some of these
ideas are finally filtering in to mainstream languages (like Swift and Rust)
where they're used to great effect, but the vast majority of programmers out
there haven't yet been exposed to them.

This post aims to demonstrate some of these features in a simple (but hopefully
not too simple) example. I'm going to write and package up a simple sorting
algorithm in both Haskell and Python, and compare the code in each. I'm choosing
Python because I like it and beginners like it, but also because it's missing
most of the features I'll be demonstrating. It's important to note I'm not
comparing Haskell and Python as languages: the Python code is just there as a
reference for people less familiar with Haskell. What's more, the comparison is
unfair, as the example deliberately plays to Haskell's strengths (so I can show
off the features I'm interested in): Haskell would come off pretty poorly if I
wanted to demo some machine-learning concept.

# The Algorithm

We'll be using a [skew heap](https://en.wikipedia.org/wiki/Skew_heap) to sort
lists in both languages. The basic idea is to repeatedly insert stuff into the
heap, and then repeatedly "pop" the smallest element from the heap until it's
empty. It's not in-place, but it is $\mathcal{O}(n \log n)$, and actually
performs pretty well in practice.

# A Tree

A Skew Heap is represented by a *binary tree*:

<style>
.column {
    float: left;
    width: 50%;
}
.row:after {
    content: "";
    display: table;
    clear: both;
}
</style>
<div class="row">
  <div class="column">
```haskell
data Tree a
  = Leaf
  | Node a (Tree a) (Tree a)
```
  </div>
  <div class="column">
```python
T = TypeVar('T')

@dataclass
class Tree(Generic[T]):
    data: T
    lchild: Optional['Tree[T]']
    rchild: Optional['Tree[T]']
```
  </div>
</div>

I want to point out the precision of the Haskell definition: a tree is either a
leaf (an empty tree), or a node, with a payload and two children. There are no
special cases, and it took us one line to write (spread to 2 here for legibility
on smaller screens).

In Python, we have to write a few more lines. We're using the nifty new
dataclasses here, but the definition is equivalent to:

```python
class Tree:
  def __init__(self, data, lchild, rchild):
    self._data = data
    self._lchild = lchild
    self._rchild = rchild
```

First things first, let's point out what Python *can* do: the type of the tree
is generic, meaning that we automatically get a "tree of integers" and a "tree
of strings" from the above type. Already we have surpassed Go in this regard. We
can also express that the children might be `None`{.python}: rather than having
a null pointer that we ourselves have to remember, we can get the compiler to do
it for us.

There are some glaring problems, though. First of all, we can't represent an
empty tree. 
