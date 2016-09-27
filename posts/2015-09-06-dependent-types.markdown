---
title: Faking dependent types in Swift
tags: Swift
description: Dependent types in Swift
---

[Dependent types](https://en.wikipedia.org/wiki/Dependent_type) are types "that depend on values". Say you had a function `f`{.scala} that took an integer. If you can write that function whereby it returns a value of type `A`{.scala} when that integer is even, or a type `B`{.scala} if the integer is odd, then you're working with dependent types. (I think. I'm not sure: if I've got it wrong [tweet me](https://twitter.com/oisdk).)

## Dependent Pretendance 

As far as I can tell, this is not possible in Swift. All variables are statically typed, and those types must be found at compile-time. As long as you're not messing around with casting:

```scala
struct A {}
struct B {}

func f(i: Int) -> AnyObject {
  return i % 2 == 0 ? A() as! AnyObject : B() as! AnyObject
}
```

You won't be able to manage it.

Now, sum types can give you something that *looks* like dependent types:

```scala
struct A {}
struct B {}

enum SumType {
  case Even(A), Odd(B)
}

func f(i: Int) -> SumType {
  return i % 2 == 0 ? .Even(A()) : .Odd(B())
}
```

But that doesn't fit the description: the thing returned is of type `SumType`{.scala}, *not* `A`{.scala} or `B`{.scala}.

That's fine, though. As with all of these highfalutin mathematical concepts in programming, you can steal some of the cool and fun *patterns* from your Haskells and Lisps and Idrises and implement them in whatever language you want.

As it happens, implementing this stuff in Swift gets you even *further* away from the formal definition of dependent types. Instead of allowing types to be decided at runtime, you end up forcing even *more* resolution and computation to happen at compile-time. Take "numbers-as-types", for instance:

```scala
protocol Nat { init() }
struct Zero : Nat {}
protocol NonZero: Nat { typealias Pred: Nat }
struct Succ<N : Nat> : NonZero { typealias Pred = N }
```

Once you encode some numbers by hand:

```scala
typealias One   = Succ<Zero>
typealias Two   = Succ<One>
typealias Three = Succ<Two>
typealias Four  = Succ<Three>
typealias Five  = Succ<Four>
typealias Six   = Succ<Five>
typealias Seven = Succ<Six>
typealias Eight = Succ<Seven>
typealias Nine  = Succ<Eight>
```

You get thinking about exactly *how much* computation you can achieve at compile time:

```scala
Sum<One, Two>.Result    // Three
Comp<Five, Nine>.Result // LT
Comp<Four, Four>.Result // EQ
```

## Sum types, divide types, multiply types ##

What I wanted, ideally, was some basic "Algebraic data types". (Today. Today was the day I made the worst pun.) I wanted to be able to add the type `One`{.scala} to the type `Two`{.scala} and get the type `Three`{.scala}. Once you can manage those, multiplication, division and all kinds of silliness are possible. I set myself some rules: all calculations must be performed at compile-time, and all calculations must work with arbitrary values.

I've not been able to manage, unfortunately. If someone could figure out how to do it, I would [love to hear it](https://twitter.com/oisdk). I've been stealing ideas from [Faking It: Simulating Dependent Types in Haskell](http://strictlypositive.org/faking.ps.gz) mainly.

Here's the kind of code that made me think it was possible:

```scala
let ar = [1, 2, 3, 4, 5].reverse()
let se = AnySequence([1, 2, 3, 4, 5]).reverse()
```

The types returned by those two methods are different. This is all to do with that protocol-oriented-programming business: the compiler will try to select the most specialised version of a method to use. So in the example above, since an array can just be indexed backwards, the compiler uses a method that returns a lazy `ReverseRandomAccessCollection`{.scala}. However, for the `AnySequence`{.scala}, the `reverse`{.scala} method has to create a whole new array.

With that in mind, we can make a protocol:

```scala
protocol BinaryOp {
  typealias A: Nat
  typealias B: Nat
}
```

Then, we can extend it, like this:

```scala
struct EQ {}
extension BinaryOp where A == B {
  typealias Result = EQ
}
```

So far, so good! The compiler will add that method to all types that conform to the `where`{.scala} clause. So if there is a concrete type that conforms to `BinaryOp`:

```scala
struct Comp<E0: Nat, E1: Nat> : BinaryOp {
  typealias A = E0
  typealias B = E1
}
```

Only instances where `A`{.scala} and `B`{.scala} are equal will get the type alias:

```scala
Comp<One, One>.Result
Comp<One, Two>.Result // Error
```

But that's not ideal. We want something that returns `NEQ`{.scala} when the types are not the same. Easy enough, right?

```scala
struct NEQ {}
extension BinaryOp {
  typealias Result = NEQ
}
```

But there's an error: `invalid redeclaration of 'Result'`{.scala}. The compiler won't allow polymorphism with typealiases. It *does* allow polymorphism with properties, though:

```scala
extension BinaryOp {
  var r: EQ { return EQ() }
}
extension BinaryOp where A == B {
  var r: NEQ { return NEQ() }
}
```

This is already a less elegant solution than the typealiases, since we're going to have to initialise things. All of the type information is available at compile-time, though, so I've not broken any of my rules.

```scala
Comp<One, One>().r // EQ
Comp<One, Two>().r // NEQ
```

How about something more complex? Instead of `EQ`{.scala} and `NEQ`{.scala}, maybe `LT`{.scala}, `GT`{.scala}, and `EQ`?

It's hard to see how it would work. Well, here's the base case:

```scala
extension BinaryOp where A == B {
  var r: EQ { return EQ() }
}
```

Then, any non-zero is bigger than zero:

```scala
struct LT {}
extension BinaryOp where A == Zero, B : NonZero {
  var r: LT { return LT() }
}
struct GT {}
extension BinaryOp where A : NonZero, B == Zero {
  var r: GT { return GT() }
}
```

If both `A`{.scala} and `B`{.scala} are nonzero, they should have a `Pred`{.scala} typealias, which we can use, recursively:

```scala
extension BinaryOp where A : NonZero, B : NonZero {
  var r: ?? {
    return Comp<A.Pred, B.Pred>().r
  }
}
```

This doesn't work. I'm fairly sure this is a definitive dead end. Here's the error: `ambiguous reference to member 'r'`{.scala}. The problem is that that error encapsulates exactly what I'm trying to achieve: I *want* the reference to be ambiguous, so it *depends* on the types of `A`{.scala} and `B`{.scala}. Most other routes I went down hit similar roadblocks:

```scala
protocol BinaryOp {
  typealias A: Nat
  typealias B: Nat
  typealias Result
  var r: Result { get }
}
```

The idea here was that you could have various implementations of `r`{.scala}, so that the `Result`{.scala} typealias would be inferred. The problem is the compiler wants to figure out what `Result`{.scala} is when you make a type that conforms to the protocol, so every type will get the default implementation. 

Yet more versions I tried all hit the `ambiguous`{.scala} error, which makes me think this kind of thing is fundamentally impossible in Swift's current form.

So I've got to break one of the rules: no more arbitrary numbers.

```scala
struct AddOne<N : Nat> {
  typealias Result = Succ<N>
}
struct AddTwo<N : Nat> {
  typealias Result = Succ<AddOne<N>.Result>
}
```
 And so on. Or:

```scala
extension Binary where A == B {
  var sub: Zero { return Zero() }
  var com: EQ { return EQ() }
}
extension Binary where A == Succ<B> {
  var sub: One { return One() }
  var com: GT { return GT() }
}
```

Which can give you subtraction.

## Let's Pretend to be Useful ##

All of that stuff is interesting, but very *very* far from being useful. 

The [length-indexed list from the other day](https://bigonotetaking.wordpress.com/2015/09/04/in-which-i-misunderstand-dependent-types/) probably is useful, though. As well as being kind of cool and safe, there are some (minor) optimisations it can do.

The other dependent type staple is the heterogenous list.

Now, this isn't just any heterogenous list: we're not writing Python here. This is a *statically typed* heterogenous list. Swift has a construct very similar to this already: a tuple!

But tuples aren't very extensible:

```scala
extension Tuple where First : Comparable {...
extension Tuple where Count == Two {...
```

And you can't work with them in terms that most lists can:

```scala
(1, "a", 2.0) + ("b", -3)
```

So that's where another tuple type can come in. A la [Rob Rix](https://twitter.com/rob_rix/status/633262294336729088), we could make a right-recursive tuple, terminated by `()`{.scala}. There'll be one overarching protocol:

```scala
protocol _AnyTuple : CustomStringConvertible {
  var tDesc: String { get }
  var count: Int { get }
  typealias Arity : Nat
}
```

And the empty tuple:

```scala
struct EmptyTuple {}

extension EmptyTuple : _AnyTuple {
  var description: String { return "()" }
  var tDesc: String { return  ")" }
  var count: Int { return 0 }
  typealias Arity = Zero
}
```

The descriptions are just there to give us a pretty printout. Here's the tuple struct:

```scala
struct NonEmptyTuple<Element, Tail : _AnyTuple> { var (head, tail): (Element, Tail) }

extension NonEmptyTuple : _AnyTuple {
  var count: Int { return tail.count + 1 }
  var description: String {
    return "(" + String(reflecting: head) + tail.tDesc
  }
  var tDesc: String {
    return ", " + String(reflecting: head) + tail.tDesc
  }
  typealias Arity = Succ<Tail.Arity>
}
```

Now, to build a tuple. Since it's right-recursive, it might look like this:

```scala
1 , "a" , 4.0 , ()
```

But there are two problems with that: first, the comma is not overloadable. That's probably a good thing. Second, it doesn't really look like a tuple.

[Joe Groff](https://twitter.com/jckarter/status/639953308401057793) solved the first problem (albeit by committing a mortal sin). Just use a unicode comma! The only one I could find that works has the delightful name of Hypodiastole.

```scala
infix operator ⸒ { associativity right precedence 90 }
```

Trying to find it in the character viewer each time was a pain, though. So I went with the boring vertical bar.

The second problem can be solved with some sneaky overloading. Here's what these functions look like:

```scala
infix operator | { associativity right precedence 90 }

func |<E, T:_AnyTuple>(lhs: E, rhs: T) -> NonEmptyTuple<E, T> {
  return NonEmptyTuple(head: lhs, tail: rhs)
}

func |<E, T>(lhs: E, rhs: T) -> NonEmptyTuple<E, NonEmptyTuple<T, EmptyTuple>> {
  return NonEmptyTuple(head: lhs, tail: NonEmptyTuple(head: rhs, tail: EmptyTuple()))
}
```

We can now, finally, build a Tuple:

```scala
(1 | 2.0 | "a" ) // (1, 2.0, "a")
```

One little wrinkle with protocols, though. If you try this:

```scala
extension NonEmptyTuple where Arity == Two {...
```

There's an error: `neither type in same-type refers to a generic parameter or associated type`{.scala}. Generally speaking, `==`{.scala} requirements in struct extensions don't work. However, they do work on protocols. So a wrapper protocol is needed:

```scala
protocol Tuple : _AnyTuple {
  typealias Head
  typealias Tail : _AnyTuple
  typealias Arity : NonZero
  var head : Head { get }
  var tail : Tail { get }
}

extension NonEmptyTuple : Tuple {}
```

Alright. Time to work with it. 

```scala
extension Tuple where
  Head : IntegerArithmeticType,
  Tail : Tuple,
  Tail.Head : IntegerArithmeticType,
  Arity == Two {
  func matSum(with: Self) -> NonEmptyTuple<Head, NonEmptyTuple<Tail.Head, EmptyTuple>> {
    let a = head + with.head
    let b = tail.head + with.tail.head
    return (a | b)
  }
}

(1 | 4).matSum(3 | 2) // (4, 6)
```

The basic advantage of this heterogenous list in Swift is its extensibility: you can treat tuples of length 2 as a type, or tuples where the third element is comparable as a type, and so on. 

```scala
extension Tuple where Tail : Tuple, Tail.Head : Comparable {
  func isSecondLessThan
    <T : Tuple where T.Tail : Tuple, T.Tail.Head == Tail.Head>
    (with: T) -> Bool {
    return tail.head < with.tail.head
  }
}

let a = (1 | 3.0 | "a" | 43)
let b = ("c" | 4.0 | 1)

a.isSecondLessThan(b)
```

Most of this stuff is madness. The custom infix unicode operator should have tipped you off to that: but it's not to say that *nothing* here is useful. Compile-time warnings are great. I think the fixed-length array works. But this tuple stuff is too hacky: it only becomes useful if there are some low-level changes to the language.

What's really useful, though, is *thinking* about types with dependency in mind. Getting familiar with what is and isn't possible to write between the `where`{.scala} and the `{`{.scala} in an extension gives you a good idea of how powerful protocols and their specialisations are.

For some extra reading, check out [DependentHaskell](https://ghc.haskell.org/trac/ghc/wiki/DependentHaskell), [Heterogenous Collections in Haskell](https://wiki.haskell.org/Heterogenous_collections), and [Strongly Typed Heterogenous Collections](http://programmers.stackexchange.com/questions/132835/is-there-a-specific-purpose-for-heterogeneous-lists). I'm muddling my way through seeing what's possible with length-indexed lists, heterogenous lists, and numeral types [over here](https://github.com/oisdk/PretendDependSwift), if you're interested.
