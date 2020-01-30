---
title: A Trie in Swift
tags: Swift, Data Structures
---

If you google "cool data structures" you'll get [this](http://stackoverflow.com/questions/500607/what-are-the-lesser-known-but-useful-data-structures) as your first result. It's a stackoverflow question: "What are the lesser known but useful data structures?". And the top answer is a Trie. I read up on them, and found out a lot of cool things about their use (as well as finding out that I'm now the kind of person who googles "cool data structures"). So I rocked on up to my playground, and got writing.

A Trie is a prefix tree. It's another recursive data structure: each Trie contains other children Tries, identifiable by their prefixes.

It's a bit of a hipster data structure, not very widely used, but it's got some useful applications. It's got set-like operations, with insertion and searching each at $O(n)$, where $n$ is the length of the sequence being searched for. A Set is the only way to go for hashable, unordered elements. But, if you've got *sequences* of hashable elements, a Trie might be for you. (one thing to note is that Sets are hashable themselves, so if the sequences you want to store are unordered, a Set of Sets is more applicable)

![A trie for keys](https://upload.wikimedia.org/wikipedia/commons/thumb/b/be/Trie_example.svg/1092px-Trie_example.svg.png)

In Swift, we can do this by having every Trie contain a dictionary of prefixes and Tries. Something like this:

```scala
public struct Trie<Element : Hashable> {
  private var children: [Element:Trie<Element>]
}
```

We don't run into the problem of structs not being allowed to be recursive here, because we don't directly store a Trie within a Trie - we store a *dictionary*, and therefore a reference to the child Tries. In this dictionary, the keys correspond to the prefixes. So how do we fill it up? Like lists, we can use the decomposition properties of generators:

```scala
extension Trie {
  private init<G : GeneratorType where G.Element == Element>(var gen: G) {
    if let head = gen.next() {
      children = [head:Trie(gen:gen)]
    } else {
      children = [:]
    }
  }
  public init
    <S : SequenceType where S.Generator.Element == Element>
    (_ seq: S) {
      self.init(gen: seq.generate())
  }
}
```

That's not really enough. That can store one sequence, but we need an `insert`{.scala} function. Here ya go:

```scala
extension Trie {
  private mutating func insert
    <G : GeneratorType where G.Element == Element>
    (var gen: G) {
      if let head = gen.next() {
        children[head]?.insert(gen) ?? {children[head] = Trie(gen: gen)}()
      }
  }
  public mutating func insert
    <S : SequenceType where S.Generator.Element == Element>
    (seq: S) {
      insert(seq.generate())
  }
}
```

There's a line in there that some may find offensive:

```scala
children[head]?.insert(gen) ?? {children[head] = Trie(gen: gen)}()
```

And, to be honest, I'm not a huge fan of it myself. It's making use of the fact that you can call mutating methods on optionals with chaining. When you do it in this example, the optional is returned by the dictionary lookup: we then want to mutate that value, if it's there, with an insertion.

If it's *not* there, though, we want to add it in, so we've got to have some way of understanding and dealing with that. We could try and extract the child Trie, like this:

```scala
if let head = gen.next() {
  if var child = children[head] {
    child.insert(gen)
  } else {
    children[head] = Trie(gen: gen)
  }
}
```

But the child there is just a copy of the actual child in the Trie we want to mutate. We could then set it back to the dictionary entry - but at this stage it feels like a lot of extra, inefficient work.

So, you can make use of the fact the functions which don't return anything actually *do* return something: a special value called `Void`{.scala}, or `()`{.scala}. Except that, in this case, it's `()?`{.scala} (or `Optional&lt;Void&gt;`{.scala}). We're not interested in the void itself, obviously, just whether or not it's `nil`{.scala}. So, one way you could use it would be like this:

```scala
if let _ = children[head]?.insert(gen) { return }
children[head] = Trie(gen: gen)
```

Or, to use `guard`{.scala}:

```scala
guard let _ = children[head]?.insert(gen) else { children[head] = Trie(gen: gen) }
```

But I think the nil coalescing operator is a little clearer, without the distraction of `let`{.scala} or `_`{.scala}.

This data structure, as you can see, has a very different feel to the list. For a start, it's much more mutable, with in-place mutating methods being a little easier than methods that return a new Trie. Also, laziness is pretty much out of the question: almost every imaginable useful method would involve evaluation of the entire Trie. (if anyone *does* have a useful way of thinking about Tries lazily, I'd love to hear it)

The contains function, the most important of them all, is here:

```scala
extension Trie {
  private func contains
    <G : GeneratorType where G.Element == Element>
    (var gen: G) -> Bool {
      return gen.next().map{self.children[$0]?.contains(gen) ?? false} ?? true
  }
  public func contains
    <S : SequenceType where S.Generator.Element == Element>
    (seq: S) -> Bool {
      return contains(seq.generate())
  }
}
```

So this uses more generators. If the generator is empty (`gen.next()`{.scala} returns `nil`{.scala}), then the Trie contains that sequence, as we have not yet found a dictionary without that element. Within the `map()`{.scala} we search for the next element from the generator. If *that* returns `nil`{.scala}, then the Trie doesn't contain that sequence. Finally, if none of that works, return whether or not the child Trie contains the rest of the generator. Let's try it out:

```scala
var jo = Trie([1, 2, 3])
jo.insert([4, 5, 6])
jo.insert([7, 8, 9])

jo.contains([4, 5, 6]) // true
jo.contains([2, 1, 3]) // false
```

There's a catch. The `contains`{.scala} method doesn't work as we'd like it to:

```scala
jo.contains([1, 2]) // true
```

Because we return `true`{.scala} *whenever* the generator runs out, our Trie "contains" every prefix of the sequences that have been inserted. This is not what we want. One way to solve this may be to return `true`{.scala} only if the last Trie found has no children. Something like this:

```scala
extension Trie {
  private func contains
    <G : GeneratorType where G.Element == Element>
    (var gen: G) -> Bool {
      return gen.next().map{self.children[$0]?.contains(gen) ?? false} ?? children.isEmpty
  }
}
```

But this doesn't really work either. what if we did `jo.insert([1, 2])`{.scala}? Now, if we check if the Trie contains `[1, 2]`{.scala}, we'll get back `false`{.scala}.

It's time for flags. We need to add an extra variable to our Trie: a Boolean, which describes whether or not that Trie represents the end of a sequence.

```scala
public struct Trie<Element : Hashable> {
  private var children: [Element:Trie<Element>]
  private var endHere : Bool
}
```

We'll also need to change our `insert`{.scala} and `init`{.scala} functions, so that when the generator returns `nil`{.scala}, `endHere`{.scala} gets initialised to `true`{.scala}.

```scala
extension Trie {
  private init<G : GeneratorType where G.Element == Element>(var gen: G) {
    if let head = gen.next() {
      (children, endHere) = ([head:Trie(gen:gen)], false)
    } else {
      (children, endHere) = ([:], true)
    }
  }
}

extension Trie {
  private mutating func insert
    <G : GeneratorType where G.Element == Element>
    (var gen: G) {
      if let head = gen.next() {
        children[head]?.insert(gen) ?? {children[head] = Trie(gen: gen)}()
      } else {
        endHere = true
      }
  }
}
```

And the contains function now returns `endHere`{.scala}, instead of true:

```scala
public extension Trie {
  private func contains
    <G : GeneratorType where G.Element == Element>
    (var gen: G) -> Bool {
      return gen.next().map{self.children[$0]?.contains(gen) ?? false} ?? endHere
  }
}
```

While we're improving the `contains`{.scala} function, we could use `guard`{.scala} to make it much more readable:

```scala
public extension Trie {
  private func contains<
    G : GeneratorType where G.Element == Element
    >(var gen: G) -> Bool {
      guard let head = gen.next() else { return endHere }
      return children[head]?.contains(gen) ?? false
  }
}
```

[Chris Eidhof gave me this idea.](https://twitter.com/chriseidhof/status/629215881843884032) (Apparently there's a Trie implementation in [Functional Programming in Swift](http://www.objc.io/books/fpinswift/), his book. I've not read it, but it's on my list. If [Advanced Swift](http://www.objc.io/books/advanced-swift/)is anything to go by, it should be fantastic.)

The objective of this Trie is to replicate all of the Set methods: Union, Intersect, etc. Most of those are manageable to build from just `insert`{.scala}, `init`{.scala}, and `contains`{.scala}, but there's one other function that comes in handy: `remove`{.scala}.

Remove is deceptively difficult. You could just walk to the end of your given sequence to remove, and switch `endHere`{.scala} from `true`{.scala} to `false`{.scala}, but that's kind of cheating. I mean, you'll be storing the same amount of information that way after a removal. No, what you need is something that deletes branches of a tree that aren't being used any more.

Again, this is a little complicated. You can't just find the head of the sequence you want to remove, and then delete all children: you may be deleting other entries along with that. You *also* can't just delete when a given Trie only contains one child: that child may branch off subsequently, or it may contain prefixes for the sequence you want to remove.

Crucially, all of the information telling you whether or not you can delete a given entry in a given Trie will come from the *children* of that Trie. What I decided to go with was this: I'll have some mutating method that does the work recursively. However, this method also *returns* a value, representing some important information for whatever called it. In this case, the `remove`{.scala} method would remove, as you'd imagine, but it will also return a Boolean, signifying whether the Trie it was called on can be removed. Since I used the normal structure of having a private method take a generator, and then a public wrapper method take a sequence, I could have the public method just discard the Boolean.

Let's go through it. Here's the signature:

```scala
private mutating func remove<
  G : GeneratorType where G.Element == Element
  >(var g: G) -> Bool {
```

No surprises there. Similar to the other methods. Then, get the head from the generator:

```scala
if let head = g.next() {
```

Within that if block is the meat of the logic, so I might skip to what happens if `g.next()`{.scala} returns `nil`{.scala} for the start:

```scala
private mutating func remove<
  G : GeneratorType where G.Element == Element
  >(var g: G) -> Bool {
    if let head = g.next() {...}
    endHere = false
    return children.isEmpty
}
```

So the sequence being removed has ended. That means that whatever Trie you're on should have its `endHere`{.scala} set to `false`{.scala}. To the user of the Trie, that's all that matters: from now on, if the contains method on that Trie is used with that sequence, it will return false.

However, to find out if you can delete the data itself, it returns `children.isEmpty`{.scala}. If it has no children, it does not hold any other sequences or information, so it can be deleted.

Now for inside the if block:

```scala
guard children[head]?.remove(g) == true else { return false }
children.removeValueForKey(head)
return !endHere && children.isEmpty
```

So it calls `remove`{.scala} on the child Trie corresponding to `head`{.scala}. That guard statement will fail for two distinct reasons: if `children`{.scala} doesn't contain `head`{.scala}, then the sequence being removed wasn't in the Trie in the first place. The method will then return false, so that no removal or mutation is done.

If it *does* contain `head`{.scala}, but the Bool returned from the remove method is `false`{.scala}, that means that its *child* is not removable, so it is also not removable, so it should return `false`{.scala}.

Otherwise, it will remove that member (`children.removeValueForKey(head)`{.scala}). Then, the Trie can decide whether or not it itself is removable: `return !endHere &amp;&amp; children.isEmpty`{.scala}. If the `endHere`{.scala} is set to true, then it is the end of some sequence: it is not removable. Otherwise, it's removable if it has no children. Here’s the whole thing, with its public version:

```scala
extension Trie {
  private mutating func remove<
    G : GeneratorType where G.Element == Element
    >(var g: G) -> Bool { // Return value signifies whether or not it can be removed
      if let head = g.next() {
        guard children[head]?.remove(g) == true else { return false }
        children.removeValueForKey(head)
        return !endHere && children.isEmpty
      }
      endHere = false
      return children.isEmpty
  }
  public mutating func remove<
    S : SequenceType where S.Generator.Element == Element
    >(seq: S) {
      remove(seq.generate())
  }
}
```

That was a little heavy. And kind of ugly. Let's lighten things up for a second, with one of the loveliest `count`{.scala} properties I've seen:

```scala
extension Trie {
  public var count: Int {
    return children.values.reduce(endHere ? 1 : 0) { $0 + $1.count }
  }
}
```

All it's really doing is counting the instances of a `true`{.scala} `endHere`{.scala}. If the current Trie is an end, then it knows that it adds one to the count (`endHere ? 1 : 0`{.scala}), and it adds that to the sum of the counts of its children.

Now then. `SequenceType`{.scala}. [Getting tree-like structures to conform to `SequenceType`{.scala} is a bit of a pain](http://airspeedvelocity.net/2015/07/22/a-persistent-tree-using-indirect-enums-in-swift/), mainly because of their recursiveness. Getting a linear representation is easy enough:

```scala
extension Trie {
  public var contents: [[Element]] {
    return children.flatMap {
      (head: Element, child: Trie<Element>) -> [[Element]] in
      child.contents.map { [head] + $0 } + (child.endHere ? [[head]] : [])
    }
  }
}
```

And then you could just return the generate method from that for your Trie's generate method.

The problem is that it's not very proper: you're translating your data structure into another data structure just to iterate through it. What you really want is something that generates each element on demand.

But it gets ugly quick. You've got to do a lot of stuff by hand which it isn't nice to do by hand, and you've got to employ some dirty tricks (like using closures as a kind of homemade `indirect`{.scala}). At any rate, here it is:

```scala
public struct TrieGenerator<Element : Hashable> : GeneratorType {
  private var children: DictionaryGenerator<Element, Trie<Element>>
  private var curHead : Element?
  private var curEnd  : Bool = false
  private var innerGen: (() -> [Element]?)?
  private mutating func update() {
    guard let (head, child) = children.next() else { innerGen = nil; return }
    curHead = head
    var g = child.generate()
    innerGen = {g.next()}
    curEnd = child.endHere
  }
  public mutating func next() -> [Element]? {
    for ; innerGen != nil; update() {
      if let next = innerGen!() {
        return [curHead!] + next
      } else if curEnd {
        curEnd = false
        return [curHead!]
      }
    }
    return nil
  }
  private init(_ from: Trie<Element>) {
    children = from.children.generate()
    update()
  }
}
```

It's got a similar logic to the lazy flatMap I did from a while ago.

The code is all available [here](https://github.com/oisdk/SwiftTrie), as a playground, or [here](https://github.com/oisdk/SwiftSequence), in SwiftSequence, where it's accompanied by some tests.
