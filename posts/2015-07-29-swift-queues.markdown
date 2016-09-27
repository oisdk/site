---
title: Deques, Queues, and Lists in Swift with Indirect
tags: Swift
description: Some pointer-based data structures in Swift
---

Recursive enums have finally arrived. Woo! The first thing to do with these is to make a recursive list:

```scala
public enum List<Element> {
  case Nil
  indirect case Cons(head: Element, tail: List<Element>)
}
```

The `head`{.scala} stores the element, and `tail`{.scala} is a reference to the rest of the list. As you can imagine, getting at the `head`{.scala} is pretty easy, while accessing elements further along is more difficult. There's a common pattern for dealing with these recursive structures: if you have a function that performs some transformation on a list, it will take the `head`{.scala}, perform that transformation on it, and then call itself recursively on the `tail`{.scala}. If it's given an empty list, it returns an empty list. For instance, here's the `map`{.haskell} function, defined in Haskell:

```haskell
map _ []     = []
map f (x:xs) = f x : map f xs
```

The two lines are analogous to a switch statement in Swift. The parameters for `map`{.haskell} are a transformation function and a list. So, the first line has `_`{.haskell} (wildcard) for the function, and `[]`{.haskell} (empty) for the list, meaning it will match any function and an empty list. It returns an empty list.

The second line matches a function (which it assigns the name `f`{.scala}) and then decomposes the list it's given into a head (`x`{.scala}) and tail (`xs`{.scala}). It then calls `f`{.scala} on the head, and prepends (the `:`{.scala} operator is prepends, also called "cons" by convention) the result to itself called recursively on the tail.

With switch statements and the `indirect`{.scala} keyword, we're getting pretty close to that level of brevity (terseness?) in Swift:

```scala
extension List {
  public func map<T>(@noescape transform: Element -> T) -> List<T> {
    switch self {
    case .Nil: return .Nil
    case let .Cons(head, tail): return
      .Cons(head: transform(head), tail: tail.map(transform))
    }
  }
}
```

We can define our own "cons", to clean it up a little. We're not allowed to use `:`{.scala}, so I went with `|>`{.scala}, which is, in my mind, reasonably representative of "cons".

```scala
infix operator |> {
  associativity right
  precedence 100
}

public func |> <T>(lhs: T, rhs: List<T>) -> List<T> {
  return .Cons(head: lhs, tail: rhs)
}

extension List {
  public func map<T>(@noescape transform: Element -> T) -> List<T> {
    switch self {
    case .Nil: return .Nil
    case let .Cons(head, tail):
      return transform(head) |> tail.map(transform)
    }
  }
}
```

Pretty soon you can start doing some elegant and exciting things with lists. The recursive pattern is *very* well suited to higher-order functions and other FP staples. Take, for instance, the `reduce`{.scala} function:

```scala
extension List {
  public func reduce<T>(initial: T, @noescape combine: (T, Element) -> T) -> T {
    switch self {
    case .Nil: return initial
    case let .Cons(h, t):
      return t.reduce(combine(initial, h), combine: combine)
    }
  }
}
```

Or a transposing function:

```scala
func transpose<T>(mat: List<List<T>>) -> List<List<T>> {
  switch mat {
  case let .Cons(x, xs) where x.isEmpty: return transpose(xs)
  case let .Cons(.Cons(x, xs), xss):
    return (x |> xss.flatMap{$0.first}) |>
      transpose(xs |> xss.map{$0.tail})
  default: return .Nil
  }
}

let jo: List<List<Int>> = [[1, 2, 3], [1, 2, 3], [1, 2, 3]]
transpose(jo) // [[1, 1, 1], [2, 2, 2], [3, 3, 3]]
```

You can do `foldr`{.scala}, which is like `reduce`{.scala}, but works in reverse:

```scala
extension List {
  func foldr<T>(initial: T, @noescape combine: (element: Element, accumulator: T) -> T) -> T {
    switch self {
    case .Nil: return initial
    case let .Cons(x, xs):
      return combine(
        element: x,
        accumulator: xs.foldr(initial, combine: combine)
      )
    }
  }
}
```

Using `foldr`{.scala}, you can get all of the non-empty subsequences of a list:

```scala
extension List {
  var subsequences: List<List<Element>> {
    switch self {
    case .Nil: return .Nil
    case let .Cons(x, xs):
      return [x] |> xs.subsequences.foldr([]) {
        (ys, r) in ys |> (x |> ys) |> r
      }
    }
  }
}
let jo: List = [1, 2, 3]
jo.subsequences // [[1], [2], [1, 2], [1, 3], [2, 3], [1, 2, 3]]
```

(these examples are all translated from the Haskell standard library) Lists are extremely fun, and some functions you would have found yourself writing on 10-15 lines can be got into 2-3. To get a better feel for playing around with lists, it's useful to have them conform to some protocols that make them easier to work with in a playground.

For instance, making a list currently looks like this:

```scala
let jo: List = 1 |> 2 |> 3 |> .Nil
```

Which is fine, and better than:

```scala
let jo: List = .Cons(head: 1, tail: .Cons(head: 2, tail: .Cons(head: 3, tail: .Nil)))
```

but still not fantastic. The obvious next step is making `List`{.scala} `ArrayLiteralConvertible`{.scala}, but there's a small catch. We don't have an `append`{.scala} function for lists (yet). So we can't, off the bat, do something like this:

```scala
extension List : ArrayLiteralConvertible {
  public init(arrayLiteral: Element...) {
    var ret: List<Element> = .Nil
    for el in arrayLiteral { ret.append(el) }
    self = ret
  }
}
```

And nor do I think we'd want to. Operations on the end of lists are slow: you have to walk along the entire list every time.

We could *reverse* the sequence we want to turn into a list, and prepend as we go. But... that's inefficient too. Sure, `Array`{.scala}s are fast to reverse, but other sequences aren't. For those that can't be reversed lazily, you're storing an extra sequence in memory unnecessarily.

But there's something that we can use: generators. In Swift, generators are like super-imperative, crazy-unsafe recursive lists. When you can the `next()`{.scala} method on a generator, you get the "head" back. Crucially, though: *the generator is left with the tail*. Making use of this fact too often will lead to bugs, but if we wrap it up in `private`{.scala}, it's a perfect fit:

```scala
extension List {
  private init<G : GeneratorType where G.Element == Element>(var gen: G) {
    if let head = gen.next() {
      self = head |> List(gen: gen)
    } else {
      self = .Nil
    }
  }
}
```

The potential bug here is kind of interesting. If, instead of an infix operator for cons, we'd had a method on `List`{.scala} that did the same thing:

```scala
extension List {
  public func prepended(with: Element) -> List<Element> {
    return .Cons(head: with, tail: self)
  }
}
```

We'd be able to curry that function in a `map()`{.scala}, and get an `init`{.scala} function that's very pretty:

```scala
extension List {
  private init<G : GeneratorType where G.Element == Element>(var g: G) {
    self = g.next().map(List(g: g).prepended) ?? .Nil
  }
}
```

But it won't run. Since the recursive call to the function is curried, it's resolved before the `g.next()`{.scala} part. Which means that, regardless of whether `g`{.scala} returns `nil`{.scala} or not, the call will be made, causing an infinite loop of sadness. To fix it, you have to make the order of operations clear: *do not* make a recursive call if `g.next()`{.scala} returns `nil`{.scala}.

```scala
extension List {
  private init<G : GeneratorType where G.Element == Element>(var gen: G) {
    if let head = gen.next() {
      self = head |> List(gen: gen)
    } else {
      self = .Nil
    }
  }
  public init<S : SequenceType where S.Generator.Element == Element>(_ seq: S) {
    self = List(gen: seq.generate())
  }
}

extension List : ArrayLiteralConvertible {
  public init(arrayLiteral: Element...) {
    self = List(arrayLiteral.generate())
  }
}
```

This all makes it easy to initialise a list. Being able to *see* the list and its contents is also important. Currently, we've got this mess:

<img class="aligncenter size-full wp-image-404" src="https://bigonotetaking.files.wordpress.com/2015/07/screen-shot-2015-07-29-at-12-12-56.png" alt="Screen Shot 2015-07-29 at 12.12.56" width="660" height="39" />

When what we really want is a comma-separated list of the contents. We also probably want some demarcation at either end, so it's easier to recognise nested lists. I'm not sure what the best demarcation would be: ideally it should be different to an Array's square brackets, but not confusing either. I went with `[:`{.scala} and `:]`{.scala} in the end, though I'm not terribly happy about it:

<img class="aligncenter size-full wp-image-406" src="https://bigonotetaking.files.wordpress.com/2015/07/screen-shot-2015-07-29-at-12-27-53.png" alt="Screen Shot 2015-07-29 at 12.27.53" width="522" height="32" />

To get that printout on the right-hand-side of your playground, you need to make your type `CustomDebugStringConvertible`{.scala}. There's one one interesting problem with this: how do you know the contents of your list are printable? You can't extend your struct to have conditional conformance, like this:

```scala
extension List (where Element : CustomDebugStringConvertible) : CustomDebugStringConvertible {...
```

However, you can't just get a string representation of something that doesn't have one. Luckily, `String`{.scala} has an initialiser that takes *anything*. It uses runtime reflection to do so. Here's what the extension ends up looking like:

```scala
extension List : CustomDebugStringConvertible {
  public var debugDescription: String {
    return"[:" + ", ".join(map{String(reflecting: $0)}) + ":]"
  }
}
```

To use the `join()`{.scala} function, of course, `List`{.scala} needs to conform to `SequenceType`{.scala}. We'll need some generator that swaps out the current `List`{.scala} struct on each iteration, and returns the head. You *could* just use `anyGenerator`{.scala} but, since it's a class, it's significantly slower than defining a new struct.

```scala
public struct ListGenerator<Element> : GeneratorType, SequenceType {
  private var list: List<Element>
  public mutating func next() -> Element? {
    switch list {
    case .Nil: return nil
    case let .Cons(head, tail):
      list = tail
      return head
    }
  }
  public func generate() -> ListGenerator { return self }
}

extension List : SequenceType {
  public func generate() -> ListGenerator<Element> {
    return ListGenerator(list: self)
  }
}
```

And you've got a `SequenceType`{.scala} that's normal-looking and easy to work with.

### Laziness
I'm not sure if this is entirely relevant here, but I *do* like laziness, so I thought I'd make a version of `List`{.scala} that was lazy. It turns out it's easy to do: in fact, it was possible before `indirect`{.scala} enums. So, starting with the standard `List`{.scala} definition:

```scala
public enum LazyList<Element> {
  case Nil
  indirect case Cons(head: Element, tail: LazyList<Element>)
}
```

Let's make it lazy. The main idea would be to defer the resolution of `tail`{.scala}. What we really want is for tail to be a function that *returns* a list, rather than a list itself.

```scala
public enum LazyList<Element> {
  case Nil
  case Cons(head: Element, tail: () -> LazyList<Element>)
}
```

This is the reason that `indirect`{.scala} isn't needed: because tail isn't a list, all that's stored in the enum is the reference to the function. This is what `indirect`{.scala} does automatically, or what the `Box`{.scala} struct did manually.

There are some more wrinkles with laziness. For instance, our old infix operator won't work:

```scala
public func |> <T>(lhs: T, rhs: LazyList<T>) -> LazyList<T> {
  return .Cons(head: lhs, tail: rhs)
}
```

Again, because tail is meant to be a function that returns a list, not a list itself. This *would* work, but not in the way we intend it:

```scala
public func |> <T>(lhs: T, rhs: LazyList<T>) -> LazyList<T> {
  return .Cons(head: lhs, tail: {rhs})
}
```

Whatever's to the right-hand-side of the operator will get resolved, and *then* put into the closure, which we don't want. For instance, this:

```scala
func printAndGiveList() -> LazyList<Int> {
  print(2)
  return .Nil
}

2 |> 1 |> printAndGiveList()
```

Will give you a "`LazyList`{.scala}", but 2 gets printed, meaning that it's not *really* behaving lazily.

`@autoclosure`{.scala} to the rescue! This is a little annotation you put before your parameters that can let you decide when to evaluate the argument.

```scala
public func |> <T>(lhs: T, @autoclosure(escaping) rhs: () -> LazyList<T>) -> LazyList<T> {
  return .Cons(head: lhs, tail: rhs)
}
```

The `escaping`{.scala} in the brackets is needed to signify that the closure will last longer than the lifetime of the scope it is declared in. If you test this new version with the `printAndGiveList()`{.scala} function, you'll see that 2 does *not* get printed. In fact, the behaviour of this operator lets us use a lot of the same code from the strict list, *without* the strictness. (The generator initialiser, for instance: the same code, if used to initialise a lazy list, will work. In fact, if the underlying sequence that the generator comes from is lazy, *that laziness is maintained in the lazy list*. That's pretty cool.)

There's an interesting point to be made, here. The usual definition for a lazy programming language is one in which functions do not evaluate their arguments until they need to. In contrast, eager languages evaluate function arguments before the body of the function. This kind of makes it seem that you could treat Swift as a totally lazy language...

At any rate, this new-and-improved operator works exactly as we want it. It's properly lazy. The rest is easy: every time `tail`{.scala} was used in `List`{.scala}, replace it with `tail()`{.scala}.

### The Deque
Lists are useful. They let you operate on their first element in $O(1)$ time, which makes a lot of sense, since you often find yourself starting there.

They've got some disadvantages, though: for one, to get to the nth element, you have to walk along n elements in the list. So while operations of the *start* are fast, operations on the end are painfully slow. And forget about efficient indexing.

This is where a Deque comes in. When you need to operate on two ends of a collection, a Deque is what you want to be using. Removal of the first and last element, prepending, and appending are all $O(1)$.

It's made up of two lists: one for the front half, and one, in reverse, for the back half. With that information we've enough to get a definition down:

```scala
public struct Deque<Element> {
  private var front, back: List<Element>
}
```

You've got to do similar things that you did to the list to get an easy-to-work-with struct. `CustomDebugStringConvertible`{.scala}, `ArrayLiteralConvertible`{.scala}, etc. It's not tremendously interesting, so here it is:

```scala
extension Deque : CustomDebugStringConvertible {
  public var debugDescription: String {
    return
      ", ".join(front.map{String(reflecting: $0)}) +
      " | " +
      ", ".join(back.reverse().map{String(reflecting: $0)})
  }
}

extension Deque {
  public init(array: [Element]) {
    let half = array.endIndex / 2
    front = List(array[0..<half])
    back = List(array[half..<array.endIndex].reverse())
  }
}

extension Deque : ArrayLiteralConvertible {
  public init(arrayLiteral: Element...) {
    self.init(array: arrayLiteral)
  }
}

extension Deque {
  public init<S : SequenceType where S.Generator.Element == Element>(_ seq: S) {
    self.init(array: Array(seq))
  }
}
```

The debug output puts a `|`{.scala} between the two lists:

<img class="aligncenter size-full wp-image-395" src="https://bigonotetaking.files.wordpress.com/2015/07/screen-shot-2015-07-28-at-21-32-44.png" alt="Screen Shot 2015-07-28 at 21.32.44" width="660" height="29" />

This makes it clear how the performance characteristics come about: because the second half is a reversed list, all of the operations on the end of the Deque are operations on the beginning of a list. And that's where lists are fast.

But there's an obvious issue. Say we take that list, and start removing the first element from it:

```scala
let a = an.tail // 2, 3 | 4, 5, 6
let b = a.tail  // 3 | 4, 5, 6
let c = b.tail  // | 4, 5, 6
let d = c.tail  // ?????
```

The front will end up being empty. The solution to this is the second important element to a Deque. It needs an invariant: if its number of elements is greater than one, neither the front list nor the back will be empty. When the invariant gets violated, it needs to fix it. We can check that the invariant has been upheld with a `switch`{.scala} statement:

```scala
extension Deque {
  private mutating func check() {
    switch (front, back) {
    case (.Nil, let .Cons(head, tail)) where !tail.isEmpty: fix()
    case (let .Cons(head, tail), .Nil) where !tail.isEmpty: fix()
    default:
      return
    }
  }
}
```

The first case is the front is empty, and the back has more than one element, and the second case is the back is empty, and the front has more than one element. To fix it, just chop off the tail of the non-empty list, reverse it, and assign it to the empty list:

```scala
extension Deque {
  private mutating func check() {
    switch (front, back) {
    case (.Nil, let .Cons(head, tail)) where !tail.isEmpty:
      (front, back) = (tail.reverse(), [head])
    case (let .Cons(head, tail), .Nil) where !tail.isEmpty:
      (back, front) = (tail.reverse(), [head])
    default:
      return
    }
  }
}
```

Now, wherever we have a mutating method that may cause a violation of the invariant, this `check`{.scala} is called. One particularly cool way to do this is by using `didSet`{.scala}:

```scala
public struct Deque<Element> {
  private var front: List<Element> { didSet { check() } }
  private var back : List<Element> { didSet { check() } }
}
```

This will call `check()`{.scala} whenever either list is mutated, ensuring you can't forget. If a *new* Deque is initialised, though, it won't be called. I don't trust myself to remember the `check()`{.scala} on every init, so we can put it into the initialiser:

```scala
  private init(_ front: List<Element>, _ back: List<Element>) {
    (self.front, self.back) = (front, back)
    check()
  }
```

This is the only initialiser so far, so it's the only one I'm allowed to call. However, there may be some cases where I *know* that the front and back are balanced. So I want a separate initialiser for those, for efficiency's sake. But it's got to be called `init`{.scala} no matter what, so how can I specify that I want to use the non-checking initialiser, over the checking one? I could have a function called something like `initialiseFromBalanced`{.scala} that returns a Deque, but I don't like that. You could use labelled arguments. [Erica Sadun has a cool post on using them with subscripts](http://ericasadun.com/2015/06/01/swift-safe-array-indexing-my-favorite-thing-of-the-new-week/), and here's what it would look like with `init`{.scala}:

```scala
extension Deque {
  private init(balancedFront: List<Element>, balancedBack: List<Element>) {
    (front, back) = (balancedFront, balancedBack)
  }
}
```

So now we have a default initialiser that automatically balances the Deque, and a specialised one that takes two lists already balanced.

There is an extra function on lists in the `check()`{.scala} function: `reverse()`{.scala}. There are a load of different ways to do it. If you're in the mood for golf:

```scala
let joanne: List = [1, 2, 3, 4, 5, 6]
joanne.reduce(.Nil) { $1 |> $0 } // 6, 5, 4, 3, 2, 1
```

Or, if you'd like to keep it recursive:

```scala
extension List {
  private func reverse(other: List<Element>) -> List<Element> {
    switch self {
    case .Nil: return other
    case let .Cons(head, tail): return tail.reverse(head |> other)
    }
  }
  public func reverse() -> List<Element> {
    return reverse(.Nil)
  }
}
```

Obviously, you want to avoid this operation as much as possible. We'll have to bear that in mind when we're adding other functions.

So what kind of operations do we want on Deques? Well, `removeFirst()`{.scala} and `removeLast()`{.scala} would be a start:

```scala
extension Deque {
  public mutating func removeFirst() -> Element {
    return front.removeFirst()
  }
  public mutating func removeLast() -> Element {
    return back.removeFirst()
  }
}
```

And the function on lists:

```scala
extension List {
  public mutating func removeFirst() -> Element {
    switch self {
    case .Nil: fatalError("Cannot call removeFirst() on an empty list")
    case let .Cons(head, tail):
      self = tail
      return head
    }
  }
}
```

The other functions are easy enough to figure out: `dropFirst()`{.scala}, `dropLast()`{.scala}, etc. And, since it conforms to `SequenceType`{.scala}, it gets all of the sequence methods from the standard library, as well. However, those methods are designed for other kinds of sequences - `Array`{.scala}s, `String.CharacterView`{.scala}s, etc. There are *much* more efficient ways to do most of them. `reverse`{.scala}, for instance, is just this:

```scala
extension Deque {
  public func reverse() -> Deque<Element> {
    return Deque(balancedFront: back, balancedBack: front)
  }
}
```

(Since reverse can't change the number of elements in either list, we can use the initialiser that takes a balanced front and back.) Other methods like `map()`{.scala}, `filter()`{.scala}, etc., will just give you back an array. If we wanted to keep the Deque, we'd have to convert it back, which involves reversing, which is expensive. So we should do our own methods for those:

```scala
extension Deque {
  public func map<T>(@noescape transform: Element -> T) -> Deque<T> {
    return Deque<T>(
      balancedFront: front.map(transform),
      balancedBack : back .map(transform)
    )
  }
}

extension Deque {
  public func filter(@noescape includeElement: Element -> Bool) -> Deque<Element> {
    return Deque(front.filter(includeElement), back.filter(includeElement))
  }
}
```

`filter()`{.scala} changes the number of elements in each list, which could cause violation of the invariant. So we use the unlabelled initialiser, which automatically `check()`{.scala}s.

Notice that we don't have to do any reversing here. This is a huge efficiency gain, but you've got to bear in mind that we're assuming the order of execution of the closures for `filter`{.scala} and `map`{.scala} don't matter. This isn't always the case. Take this function, which is supposed to skip two elements of a sequence:

```scala
var i = 0
[Int](1...10).filter { _ in i++ % 3 == 0 } // [1, 4, 7, 10]
```

It won't work for a Deque:

```scala
Deque(1...10).filter { _ in i++ % 3 == 0 } // 1, 4 | 6, 9
```

There's been talk of a `@pure`{.scala} attribute. The idea is this: put it before your function or closure name, and the compiler will verify that it has no side effects. It can only use its arguments as variables, or call other `@pure`{.scala} functions. It would be very useful here, as it wouldn't allow the `i`{.scala} to be used by `filter`{.scala}. Without it, you'll probably just have to mention in the docs that the order of execution is not knowable.

For completeness' sake, there are also `flatMap()`{.scala}s for the Deque, implemented in a similar fashion to the functions above:

```scala
extension Deque {
  public func flatMap<T>(@noescape transform: Element -> Deque<T>) -> Deque<T> {
    return Deque<T>(
      front.flatMap{List(transform($0))},
      back .flatMap{List(transform($0).reverse())}
    )
  }

  public func flatMap<T>(@noescape transform: Element -> T?) -> Deque<T> {
    return Deque<T>(
      front.flatMap(transform),
      back .flatMap(transform)
    )
  }
}
```

All of this code is available as a playground, [here](https://github.com/oisdk/Deques-Queues-and-Lists-in-Swift-with-indirect). These two structs are also implemented a little more fully in [SwiftSequence](https://github.com/oisdk/SwiftSequence).

Since the only real constitutive part of the Deque is a list, it's probably possible to implement it lazily, by just substituting in `LazyList`{.scala}s. Or, if you were feeling adventurous, you could have one of the lists lazy, and one strict. This isn't as crazy as it sounds: `reverse()`{.scala} can *only* be performed eagerly, since the entire list needs to be walked to get to the last element. So the front and back lists have different functions (slightly). Also, because of the lazy initialisation of `LazyList`{.scala}, swapping between lazy and strict needn't be very expensive. I'll leave it up to someone else to try, though.
