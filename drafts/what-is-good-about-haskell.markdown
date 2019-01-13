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

This post is not meant to say "Haskell is great, and your language sucks"! quite
the opposite, actually: all of the features I'm going to talk about could be
immediately lifted and added to whatever other language you care to think of.
Some of them already exist in mainstream languages today, and most of them don't
even (really) come from Haskell!

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
class Tree:
  def __init__(self, is_node, data, lchild, rchild):
    self._is_node = is_node
    self._data = data
    self._lchild = lchild
    self._rchild = rchild
    
def leaf():
  return Tree(False, None, None, None)

def node(data, lchild, rchild):
  return Tree(True, data, lchild, rchild)
```
  </div>
</div>

I want to point out the precision of the Haskell definition: a tree is either a
leaf (an empty tree), or a node, with a payload and two children. There are no
special cases, and it took us one line to write (spread to 2 here for legibility
on smaller screens).

In Python, we have to write a few more lines[^dataclasses]. This representation
uses the `_is_node` field is `False` for an empty tree (a leaf). If it's `True`,
the other fields are filled. We write some helper functions to give us
constructors like the leaf and node ones for the Haskell example.

This isn't the standard definition of a binary tree in Python, in fact it might
looks a little weird to most Python people. Let's run through some alternatives
and their issues.

#. The standard definition:

   ```python
   class Tree:
     def __init__(self, data, lchild, rchild):
       self._data = data
       self._lchild = lchild
       self._rchild = rchild
   ```

   Instead of having a separate field for "is this a leaf or a node", the empty
   tree is simply `None`:

   ```python
   def leaf():
       return None
   ```
   
   With this approach, if we define any *methods* on a tree, they won't work on
   the empty tree!

   ```python
   >>> leaf().size()
   AttributeError: 'NoneType' object has no attribute 'size'
   ```

#. We'll do inheritance! Python even has a handy `abc` library to help us with
   some of this:

   ```python
   from abc import ABC, abstractmethod
 
   class Tree(ABC):
       @abstractmethod
       def size(self):
           raise NotImlemented
 
   class Leaf(Tree):
       def __init__(self):
           pass
 
       def size(self):
           return 0
 
   class Node(Tree):
       def __init__(self, data, lchild, rchild):
           self._data = data
           self._lchild = lchild
           self._rchild = rchild
 
       def size(self):
           return 1 + self._lchild.size() + self._rchild.size()
   ```
   
   Methods will now work on an empty tree, but we're faced with 2 problems:
   first, this is very verbose, and pretty complex. Secondly, we can't write a
   mutating method which changes a tree from a leaf to a node. In other words,
   we can't write an `insert` method!
   
#. We won't represent a leaf as the whole *tree* being `None`, just the data!

   ```python
   def leaf():
       return Tree(None, None, None)
   ```
   
   This (surprisingly) pops up in a few places. While it solves the problem of
   methods, and the mutation problem, it has a serious bug. We can't have `None`
   as an element in the tree! In other words, if we ask our eventual algorithm
   to sort a list which contains `None`, it will silently discard some of the
   list, returning the wrong answer.

[^dataclasses]: Yes, I know about the new dataclasses feature. However, it's
wrapped up with the (also new) type hints module, and as such is much more
complicated to use. As the purpose of the Python code here is to provide
something of a lingua franca for non-Haskellers, I decided against using it.
That said, the problems outlined are *not* solved by dataclasses.

There are yet more options (using a wrapper class), none of them ideal. Another
thing to point out is that, even with our definition with a tag, we can only
represent types with 2 possible states. If there was another type of node in the
tree, we couldn't simply use a boolean tag: we'd have to switch to integers (and
remember the meaning of each integer), or strings! Yuck!

What Python is fundamentally missing here is *algebraic data types*. This is a
way of building up all of your types out of products ("my type has this *and*
this") and sums ("my type is this *or* this"). Python can do products perfectly
well: that's what classes are. The tree class itself is the product of `Bool`,
`data`, `Tree`, and `Tree`. However it's missing an *entire half of the
equation*! This is why you just can't express binary trees as cleanly as you can
in Swift, Haskell, OCaml, etc. Python, as well as a host of other languages like
Go, Java, etc, will let you express *one* kind of "sum" type: "or nothing" (the
null pointer). However, it's clunky and poorly handled in all of those languages
(the method problems above demonstrate the issues in Python), and doesn't work
for anything other than that one special case.

Again, there's nothing about algebraic data types that makes them ill-suited to
mainstream or imperative languages. Swift uses them, and [people love
them](https://www.caseyliss.com/2016/2/27/swift-enums)!

# A Function

The core operation on skew heaps is the *skew merge*.

<div class="row">
  <div class="column">
```haskell
merge :: Ord a => Tree a -> Tree a -> Tree a
merge Leaf ys = ys
merge xs Leaf = xs
merge xs@(Node x xl xr) ys@(Node y yl yr)
   | x <= y    = Node x (merge ys xr) xl
   | otherwise = Node y (merge xs yr) yl
```
  </div>
  <div class="column">
```python
def merge(lhs, rhs):
  if not lhs._is_node:
    return rhs
  if not rhs._is_node:
    return lhs
  if lhs._data <= rhs._data:
    return Tree(lhs._data,
                merge(rhs, lhs._rchild),
                lhs._lchild)
  else:
    return Tree(rhs._data,
                merge(lhs, rhs._rchild),
                rhs._lchild)
```
  </div>
</div>

The standout feature here is pattern matching. In Haskell, we're able to write
the function as we might describe it: "in this case, I'll do this, in this other
case, I'll do this, etc.". In Python, we are forced to think of the truth tables
and sequential testing. What do I mean by truth tables? Consider the following
version of the Python function above:

```python
def merge(lhs, rhs):
  if lhs._is_node:
    if rhs._is_node:
      if lhs._data <= rhs._data:
        return Tree(lhs._data,
                    merge(rhs, lhs._rchild),
                    lhs._lchild)
      else:
        return Tree(rhs._data,
                    merge(lhs, rhs._rchild),
                    rhs._lchild)
    else:
      return lhs
  else:
    return rhs
```

You may even write this version first: it initially seems more natural (because
`_is_node` is used in the positive). Here's the question, though: does it do the
same thing as the previous version? Are you *sure*? Which else is connected to
which if? Does every if have an else? (some linters will suggest you *remove*
some of the elses above, since the if-clause has a `return` statement in it!)

The fact of the matter is that we are forced to do truth tables of every
condition in our minds, rather than *saying what we mean* (as we do in the
Haskell version).

The other thing we're saved from in the Haskell version is accessing undefined
fields. In the Python function, we know accessing `lhs._data` is correct since
we verified that `lhs` is a node. But the logic to do this verification is
complex: we checked if it *wasn't* a node, and returned if that was true... so
if it *is true* that `lhs` *isn't* a node, we would have returned, but we
didn't, so...

Bear in mind all of these logic checks happened four lines before the actual
access: this can get much uglier in practice! Compare this to the Haskell
version: *we only get to bind variables if we're sure they exist*. The syntax
itself prevents us from accessing fields which aren't defined, in a simple way.

Pattern matching has existed for years in many different forms: even C has
switch statements. The added feature of destructuring is available in languages
like Swift, Rust, and the whole ML family. Ask for it in your language today!

Now that we have that function, we get to define others in terms of it:

<div class="row">
  <div class="column">
```haskell
insert :: Ord a => a -> Tree a -> Tree a
insert x = merge (Node x Leaf Leaf)
```
  </div>
  <div class="column">
```python
def insert(element, tree):
    tree.__dict__ = merge(node(element, leaf(), leaf()),
                          tree).__dict__.copy()
```
  </div>
</div>


# When Things Go Wrong

The next function is "pop-min":

<div class="row">
  <div class="column">
```haskell
popMin :: Ord a => Tree a -> Maybe (a, Tree a)
popMin Leaf = Nothing
popMin (Node x xl xr) = Just (x, merge xl xr)
```
  </div>
  <div class="column">
```python
def popMin(tree):
  if tree._is_node:
    res = tree._data
    tree.__dict__ = merge(tree._lchild, tree._rchild).__dict__.copy()
    return res
  else:
    raise IndexError
```
  </div>
</div>

At first glance, this function should be right at home in Python. It *mutates*
its input, and it has an error case. Isn't Haskell cumbersome at handling
errors and state?

Aside from the verbosity, the Python version actually works pretty well. The
only wart is that we use `IndexError`: this doesn't seem suited to what we're
doing, but it's what the Python standard library uses for its own `pop` function
on lists.

# Gluing It All Together

The main part of our task is now done: all that is left is to glue the various
bits and pieces together. Remember, the overall algorithm builds up the heap
from a list, and then tears it down using `popMin`. First, then, to build up the
heap.

<div class="row">
  <div class="column">
```haskell
listToHeap :: Ord a => [a] -> Tree a
listToHeap = foldr insert Leaf
```
  </div>
  <div class="column">
```python
def listToHeap(elements):
  res = leaf()
  for el in elements:
    insert(el, res)
  return res
```
  </div>
</div>

The pattern of "building up something from a list" is a common one in *all*
programming languages. So why, then, doesn't Python have a function to do it for
us (rather than writing the for-loop by hand)?

The answer is that Python *does*: it's called `reduce`, but it's [been relegated
to functools](https://docs.python.org/3/library/functools.html#functools.reduce)
since Python 3. However, it wouldn't work for our use case: the `insert` function
we wrote is *mutating*, which doesn't gel well with `reduce`.

This is what people mean by "compositionality" when they talk about functional
programming: if you keep things simple, and build things out of functions,
they'll tend to glue together *well*, without having to write any glue code
yourself. The next function, `heapToList`, illustrates this even more so:


<div class="row">
  <div class="column">
```haskell
heapToList :: Ord a => Tree a -> [a]
heapToList = unfoldr popMin
```
  </div>
  <div class="column">
```python
def heapToList(tree):
  res = []
  try:
    while True:
      res.append(popMin(tree))
  except IndexError:
    return res
```
  </div>
</div>

 Again, building a list from something else is *also* a very common pattern.
 And, again, Python does indeed have a function which abstracts this pattern for
 us: [`iter`](https://docs.python.org/3/library/functions.html#iter) has an
 overload which will repeatedly call a function until it hits a sentinel value.
 But this doesn't fit with the rest of the iterator model! Most iterators are
 terminated with the `StopIteration` exception; ours (like the `pop` function on
 lists) is terminated by the `IndexError` exception; and this function excepts a
 third version, terminated by a sentinel! 

Finally, we should be able to write our sorting method:

<div class="row">
  <div class="column">
```haskell
sort :: Ord a => [a] -> [a]
sort = heapToList . listToHeap
```
  </div>
  <div class="column">
```python
def sort(elements):
  return heapToList(listToHeap(elements))
```
  </div>
</div>

This is just driving home the point: programs work *well* when they're built out
of functions, and you *want* your language to encourage you to build things out
of functions. In this case, the `sort` function is built out of two smaller
ones: it's the *essence* of function composition.

# Laziness

Laziness is one of the most misunderstood and poorly taught elements of Haskell.
I tend to think that people overstate how hard it makes reasoning about space:
it actually follows pretty straightforward rules, which you can generally step
through in yourself (compared to, for instance, rewrite rules, which are often
black magic!)

The other element of laziness is that, in modern programming, people will tend
to use it anyway. Python is a great example: the
[itertools](https://docs.python.org/3/library/itertools.html) library is almost
entirely lazy. Actually making use of the laziness, though, is difficult and
error-prone. Above, for instance, the `heapToList` function is lazy in Haskell,
but strict in Python. Converting it to a lazy version is not the most difficult
thing in the world:

```python
def heapToList(tree):
  try:
    while True:
      yield popMin(tree)
  except IndexError:
    pass
```

But now, suddenly, the entire list API won't work. What's more, if we try and
access the *first* element of the returned value, we mutate the whole thing:
anyone else looking at the output of the generator will have it mutated out from
under them!

Haskell's list API handles all of this stuff *automatically*. If you want the
first element in the list, it will calculate it. No-one else's list is mutated.
If you ask for that same element again, it won't calculate it again! You get all
the benefits of generators *with* the benefits of lists (except indexing, of
course).

# Testing
# Benchmarking
