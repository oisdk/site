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
off the features I'm interested in): it wouldn't be difficult to pick an example
that makes Python look good and Haskell look poor.

This post is not meant to say "Haskell is great, and your language sucks"!
It's not even really about Haskell: much of what I'm talking about here applies
equally well to Ocaml, Rust, etc.
I'm really writing this as a response to the notion that functional features are
somehow experimental, overly complex, or ultimately compromised.
As a result of that idea, I feel like these features are left out of a lot of
modern languages which would benefit from them.
There exists a small set of simple, battle-tested PL ideas, which have been used
for nearly forty years now: this post aims to demonstrate them, and argue for
their inclusion in every general-purpose programming language that's being
designed today.

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
special cases, and it took us one line to write (spread to 3 here for legibility
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

# A Word on Types

I haven't mentioned Haskell's type system so far, as it's been quite unobtrusive
in the examples.
And that's kind of the point: despite more complex examples you'll see online
demonstrating the power of type classes and higher-kinded types, Haskell's type
system *excels* in these simpler cases.

```haskell
merge :: Ord a => Tree a -> Tree a -> Tree a
```

Without much ceremony, this signature tells us:

#. The function takes two trees, and returns a third.
#. Both trees have to be filled with the same types of elements.
#. Those elements must have an order defined on them.

# Type Inference

I feel a lot of people miss the point of this particular feature.
Technically speaking, this feature allows us to write fewer type signatures, as
Haskell will be able to guess most of them. 
Coming from something like Java, you might think that that's an opportunity to
shorten up some verbose code.
It's not!
You'll rarely find a Haskell program these days missing top-level type
signatures: it's easier to read a program with explicit type signatures, so
people are advised to put them as much as possible.

(Amusingly, I often find older Haskell code snippets which are entirely devoid
of type signatures.
It seems that programmers were so excited about Hindley-Milner type inference
that they would put it to the test as often as they could.)

Type inference in Haskell is actually useful in a different way.
First, if I write the *implementation* of the `merge` function, the compiler
will tell *me* the signature, which is extremely helpful for more complex
examples.
Take the following, for instance:

```haskell
f x = ((x * 2) ^ 3) / 4
```

Remembering precisely which numeric type `x` needs to be is a little difficult
(`Floating`? `Real`? `Fractional`?), but if I just ask the compiler it will tell
me without difficulty.

The second use is kind of the opposite: if I have a hole in my program where I
need to fill in some code, Haskell can help me along by telling me the *type* of
that hole automatically.
This is often enough information to figure out the entire implementation!
In fact, there are some programs which will use this capability of the type
checker to fill in the hole with valid programs, synthesising your code for you.

So often strong type systems can make you feel like you're fighting more and
more against the compiler.
I hope these couple examples show that it doesn't have to be that way.

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

At first glance, this function should be right at home in Python.
It *mutates* its input, and it has an error case.
The code we've written here for Python is pretty idiomatic, also: other than the
ugly deep copy, we're basically just mutating the object, and using an exception
for the exceptional state (when the tree is empty).
Even the exception we use is the same exception as when you try and `pop()` from
an empty list.

The Haskell code here mainly demonstrates a difference in API style you'll see
between the two languages.
If something isn't found, we just use `Maybe`.
And instead of mutating the original variable, we return the new state in the
second part of a tuple.
What's nice about this is that we're only using simple core features like
algebraic data types to emulate pretty complex features like exceptions in
Python.

You may have heard that "Haskell uses monads to do mutation and exceptions".
This is not true.
Yes, state and exceptions have patterns which technically speaking are
"monadic".
But make no mistake: when we want to model "exceptions" in Haskell, we really
just return a maybe (or an either).
And when we want to do "mutation", we return a tuple, where the second element
is the updated state.
You don't have to understand monads to use them, and you certainly don't "need"
monads to do them.
To drive the point home, the above code could actually equivalently have a type
which mentions "the state monad" and "the maybe monad":

```haskell
popMin :: Ord a => StateT (Tree a) Maybe a
```

But there's no need to!

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

To my eye, the Haskell code here is significantly more "readable" than the Python.
I know that's a very subjective judgement, but `foldr` is a function so often
used that it's immediately clear what's happening in this example.

Why didn't we use a similar function in Python, then?
We actually could have: python does have an equivalent to `foldr`, called
`reduce` (it's [been relegated to
functools](https://docs.python.org/3/library/functools.html#functools.reduce)
since Python 3 (also technically it's equivalent to `foldl`, not `foldr`)).
We're encouraged *not* to use it, though: the more pythonic code uses a for
loop.
Also, it wouldn't work for our use case: the `insert` function we wrote is
*mutating*, which doesn't gel well with `reduce`.

I think this demonstrates another benefit of simple, functional APIs. 
If you keep things simple, and build things out of functions, they'll tend to
glue together *well*, without having to write any glue code yourself. 
The for loop, in my opinion, is "glue code".
The next function, `heapToList`, illustrates this even more so:

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

Again, things are kept simple in the Haskell example.
We've stuck to data types and functions, and these data types and functions mesh
well with each other.
You might be aware that there's some deep and interesting mathematics behind the
`foldr` and `unfoldr` functions going on, and [how they
relate](https://kseo.github.io/posts/2016-12-12-unfold-and-fold.html).
We don't need to know any of that here, though: they just work together well.

Again, Python does have a function which is equivalent to `unfoldr`:
[`iter`](https://docs.python.org/3/library/functions.html#iter) has an overload
which will repeatedly call a function until it hits a sentinel value.
But this doesn't fit with the rest of the iterator model! Most iterators are
terminated with the `StopIteration` exception; ours (like the `pop` function on
lists) is terminated by the `IndexError` exception; and this function excepts a
third version, terminated by a sentinel! 

Finally, let's write `sort`:

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

So I fully admit that laziness is one of the features of Haskell that does have
downsides.
I don't think every language should be lazy, but I did want to say a little
about it in regards to the sorting example here.

I tend to think that people overstate how hard it makes reasoning about space:
it actually follows pretty straightforward rules, which you can generally step
through in yourself (compared to, for instance, rewrite rules, which are often
black magic!)

In modern programming, people will tend to use laziness it anyway.
Python is a great example: the
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

Laziness fundamentally makes this more reusable.
Take our `popMin` function: if we just want to view the smallest element,
without reconstructing the rest of the tree, we can actually use `popMin` as-is.
If we don't use the second element of the tuple we don't pay for it.
In Python, we need to write a second function.

# Testing

Testing the `sort` function in Haskell is ridiculously easy.
Say we have an example sorting function that we trust, maybe a slow but obvious
insertion sort, and we want to make sure that our fast heap sort here does the
same thing.
This is the test:

```haskell
quickCheck (\xs -> sort (xs :: [Int]) === insertionSort xs)
```

In that single line, the
[QuickCheck](https://hackage.haskell.org/package/QuickCheck) library will
automatically generate random input, run each sort function on it, and compare
the two outputs, giving a rich diff if they don't match.

# Conclusion

This post was meant to show a few features like pattern-matching, algebraic data
types, and function-based APIs in a good light.
These ideas aren't revolutionary any more, and plenty of languages have them,
but unfortunately several languages don't.
Hopefully the example here illustrates a little why these features are good, and
pushes back against the idea that algebraic data types are too complex for
mainstream languages.
