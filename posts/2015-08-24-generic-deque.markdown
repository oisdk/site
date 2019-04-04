---
title: Using Protocols to Build a (very) Generic Deque 
tags: Swift, Data Structures
---

(Download the playground to use the code and see the outputs)

This post is an update on a [previous implementation of a
Deque](https://bigonotetaking.wordpress.com/2015/08/09/yet-another-root-of-all-evil/).
A full implementation of this Deque is available
[here](https://github.com/oisdk/SwiftDataStructures/blob/master/SwiftDataStructures/Deque.swift).

A Deque is a data structure comprised of two stacks, facing opposite directions.
In this way, operations at either end of the Deque have the same complexity as
operations on one end of the underlying stack. This implementation uses two
arrays, with the front reversed: appending, prepending, and removal of the first
and last elements are all (amortized) O(1).

The standard library has three `Array`{.scala} structs: `Array`{.scala}, `ArraySlice`{.scala}, and 
`ContiguousArray`{.scala}. They all have the same interface, with different underlying 
implementations. An `Array`{.scala} is a standard vector-like structure, which allows
O(1) amortized appending, fast iteration, etc. A `ContiguousArray`{.scala} has stricter
rules about contiguity, but it's not bridged to Objective-C.

```scala
let array  = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
let cArray: ContiguousArray = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
```

An `ArraySlice`{.scala} is a reference into an `Array`{.scala} or `ContiguousArray`{.scala}, for more
efficient slicing. All the information an `ArraySlice`{.scala} contains is the beginning
and end points of the slice (as well as any changes made to the slice separate 
from the array)

```scala
let slice = array[0..<6]
```

To replicate these semantics in a Deque requires three separate structs: one with
an `Array`{.scala} as the stack, another with an `ArraySlice`{.scala} as the stack, and a third 
with a `ContiguousArray`{.scala}. The standard library seems to duplicate the structs, 
along with their methods and properties.

It would be much nicer to just define a protocol that represented the 
*difference* between the deque types: then you could just write the methods and 
properties once, on top of it. Something like this:

```scala
protocol DequeType {
  typealias Container : RangeReplaceableCollectionType, MutableSliceable
  var front: Container { get set }
  var back : Container { get set }
  init()
}
```

There’s one problem with this: both stacks need to be made public. It would be 
much nicer to hide the stacks (especially since an invariant needs to be
checked and maintained on every mutation). If anyone has an idea of how to
accomplish that, [tweet me](https://twitter.com/oisdk).

The first method to implement is a subscript. Indexing is difficult, because the
front stack will be reversed, so the index used to get in to the Deque will need
to be translated into an equivalent index in the array.

Any (valid) index will point into either the front or back queue, and the
transformations applied to it in each case is different. If it’s in the front, 
the end result will look like `front[front.endIndex - 1 - i]`{.scala}, whereas if it’s in
the back, it should be `back[i - front.endIndex]`{.scala}. There’s nothing specified 
about the Containers except that they’re `RangeReplaceableCollectionType`{.scala} and
`MutableSliceable`{.scala}, so the index types will have to be as generic as possible. 
(you could specify `where Index == Int`{.scala}, but that’s more specific than needed, 
and not very extensible.)

Both of those transformations are subtractions, an operation that's possible on
`RandomAccessIndexType`s with the `advancedBy`{.scala} method. `advancedBy`{.scala} takes the 
associated `Distance`{.scala} type of the `RandomAccessIndexType`{.scala}. That's enough
information to figure out that the Deque's index type must be the same as the
Distance of the Index of the Container.

```scala
extension DequeType {
  typealias Index = Container.Index.Distance
}
```
The method that will translate an index into the relevant index in the stacks
will return an enum:
```scala
public enum IndexLocation<I> {
  case Front(I), Back(I)
}
```

Then, the translate method itself:

```scala
extension DequeType where
  Container.Index : RandomAccessIndexType,
  Container.Index.Distance : ForwardIndexType {
  
  private func translate(i: Container.Index.Distance)
    -> IndexLocation<Container.Index> {
    return i < front.count ?
      .Front(front.endIndex.predecessor().advancedBy(-i)) :
      .Back(back.startIndex.advancedBy(i - front.count))
  }
}
```
This performs two steps:
1. Check which stack it's in.
2. Subtract in the appropriate order

```scala
let d: Deque = [1, 2, 3, 4, 5, 6] // [1, 2, 3 | 4, 5, 6]

d.translate(0) // Front: 2
d.translate(4) // Back: 1
```

This means that the logic for converting distance to index is separated from the 
logic for actual indexing. Great! Here’s the indexing:

```scala
extension DequeType where
  Container.Index : RandomAccessIndexType,
  Container.Index.Distance : ForwardIndexType {
  var startIndex: Container.Index.Distance { return 0 }
  var endIndex  : Container.Index.Distance { return front.count + back.count }
  subscript(i: Container.Index.Distance) -> Container.Generator.Element {
    get {
      switch translate(i) {
      case let .Front(i): return front[i]
      case let .Back(i): return back[i]
      }
    } set {
      switch translate(i) {
      case let .Front(i): front[i] = newValue
      case let .Back(i): back[i] = newValue
      }
    }
  }
}
```

This makes things much easier to test and debug.

Here's where the power of protocols becomes obvious. If you go back to the 
original definition of `DequeType`{.scala}, you can add `Indexable`{.scala}. It may seem like now
only indexable things can conform, but what happens in practice is that when 
`Indexable`{.scala} looks for its requirements, *it can use the implementations in
DequeType*. That means that we’ve just made anything that can conform to
`DequeType`{.scala} indexable. That’s awesome.

Next job is ranged indices. This is a good bit more complicated than the 
individual indices, so it definitely will benefit from being separated into a 
translate method:

```scala
extension DequeType where
  Container.Index : RandomAccessIndexType,
  Container.Index.Distance : BidirectionalIndexType {
  
  private func translate
    (i: Range<Container.Index.Distance>)
    -> IndexRangeLocation<Container.Index> {
      if i.endIndex <= front.count {
        let s = front.endIndex.advancedBy(-i.endIndex)
        if s == front.startIndex && i.isEmpty { return .Between }
        let e = front.endIndex.advancedBy(-i.startIndex)
        return .Front(s..<e)
      }
      if i.startIndex >= front.count {
        let s = back.startIndex.advancedBy(i.startIndex - front.count)
        let e = back.startIndex.advancedBy(i.endIndex - front.count)
        return .Back(s..<e)
      }
      let f = front.startIndex..<front.endIndex.advancedBy(-i.startIndex)
      let b = back.startIndex..<back.startIndex.advancedBy(i.endIndex - front.count)
      return .Over(f, b)
  }
}

let otherDeque: Deque = [0, 1, 2, 3, 4, 5] // [0, 1, 2 | 3, 4, 5]

otherDeque.translate(0...2) // Front: 0..<3
otherDeque.translate(4...5) // Back: 1..<3
otherDeque.translate(2...5) // Over: 0..<1, 0..<3
otherDeque.translate(3..<3) // Between
```

The invariant that must be maintained in the deque is this: if either stack has
more than one element, the other cannot be empty. If the invariant is violated, 
the longer stack is reversed, and put in place of the shorter.

```scala
public enum Balance {
  case FrontEmpty, BackEmpty, Balanced
}

extension DequeType {
  
  public var balance: Balance {
    let (f, b) = (front.count, back.count)
    if f == 0 {
      if b > 1 {
        return .FrontEmpty
      }
    } else if b == 0 {
      if f > 1 {
        return .BackEmpty
      }
    }
    return .Balanced
  }
  
  public var isBalanced: Bool {
    return balance == .Balanced
  }
}
```

A deque is a good data structure for certain uses, especially those that require
popping and appending from either end. `popFirst()`{.scala} and `popLast()`{.scala} aren't
included in the standard `RangeReplaceableCollectionType`{.scala}, though, so we'll have 
to add our own.

```scala
extension RangeReplaceableCollectionType where Index : BidirectionalIndexType {
  private mutating func popLast() -> Generator.Element? {
    return isEmpty ? nil : removeLast()
  }
}

var mutableDeque: Deque = [0, 1, 2, 3, 4, 5]
mutableDeque.popLast() // 5
mutableDeque           // [0, 1, 2 | 3, 4]

extension DequeType where Container.Index : BidirectionalIndexType {
  public mutating func popLast() -> Container.Generator.Element? {
    return back.popLast()
  }
}
```

The method needs to include `check()`{.scala}, which we can do with `defer`

```scala
mutating func popLast() -> Container.Generator.Element? {
  defer { check() }
  return back.popLast()
}

mutableDeque.popLast() // 4
mutableDeque           // [0, 1, 2 | 3]
mutableDeque.popLast() // 3
mutableDeque           // [0 | 1, 2]
```

You also can't just pop from the back queue in `popLast()`{.scala}, because it may be the
case that the front stack has one element left

```scala
mutating func popLast() -> Container.Generator.Element? {
  defer { check() }
  return back.popLast() ?? front.popLast()
}

mutableDeque.popLast() // 2
mutableDeque.popLast() // 1
mutableDeque           // [0|]
mutableDeque.popLast() // 0
mutableDeque           // [|]
mutableDeque.popLast() // nil
```

The rest of the Deque was easy, with little to no repetition. Using protocols in
this way was really surprisingly powerful: now, you can define a `DequeType`{.scala},
with full access to all of the collection methods, all the way up to
`RangeReplaceableCollectionType`{.scala}, in five lines:

```scala
public struct Deque<Element> : DequeType {
  public var front, back: [Element]
  public typealias SubSequence = DequeSlice<Element>
  public init() { (front, back) = ([], []) }
}

public struct DequeSlice<Element> : DequeType {
  public var front, back: ArraySlice<Element>
  public typealias SubSequence = DequeSlice
  public init() { (front, back) = ([], []) }
}
```

There’s no performance hit, there’s no safety problems. I only have one version 
of code to test, one version to change, one version to read. It’s completely 
extensible: you could use any kind of stack for the front and back. Even another 
Deque, if you were so inclined:

```scala
struct DequeDeque<Element> : DequeType {
  var front, back: Deque<Element>
  typealias SubSequence = DequeDequeSlice<Element>
  init() { front = Deque(); back = Deque() }
}

struct DequeDequeSlice<Element> : DequeType {
  var front, back: DequeSlice<Element>
  typealias SubSequence = DequeDequeSlice
  init() { front = DequeSlice(); back = DequeSlice() }
}

let dd: DequeDeque = [1, 2, 3, 4, 5, 6, 7, 8]
dd.front // [4 | 3, 2, 1]
dd.back  // [5 | 6, 7, 8]
```

Woo protocols!
