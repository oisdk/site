---
title: Swift Protocols: A Strategy
tags: Swift
description: Exploring protocols in Swift
---

### A Misguided, Over-Simplified Strategy

# It Makes Sense to Me, so...
So I've been drinking the Protocol-Oriented-Programming gatorade for a while now. I've taken it to the extreme a little: you won't find a class in pretty much any of my code these days. So, before I pull it back a little, I thought I'd put down my strategy so far for how to handle these protocol things.

To give you an idea of where I'm coming from: I never really understood object-oriented programming. It never clicked with me. I mean, I know the basic ideas, but they were never internalised. On the other hand, functional programming was a breeze (by comparison). I should be clear: by FP I don't really mean monads or functors or applicative functors and monoids and commands and arrows and lenses and flux capacitors. I think everyone has a relatively difficult time wrapping their heads around that stuff.

I mean the *patterns* you see in FP. Pure functions - of course - but other things, also. Things that aren't strictly FP, but just tend to be found among the FP: type classes, currying, immutability, declarative-ness, laziness, higher-order functions. Contrast that to the patterns you find in OOP: the delegate pattern, class inheritance, single-dependancy whatnot (I can't even name them because I'm sure I'm mixing up and misunderstanding them).

Now, there are probably good reasons why I understand FP a little easier than OOP (or I think I do). OOP was what I saw first: when I began coding, it was in OOP. By the time I tried to understand, say, higher-order functions, I had already gotten my head around functions, types, variables, etc. Whereas when I first read "Python is an *object-oriented* programming language", I had written my first hello world a few weeks before.

On top of that, I'm a hobbyist - I don't like making things that really work, because that's annoying. I am *very good* at finding you Fibonacci numbers. I don't need to know about state, or IO, so I'm perfectly fine in the clean, pleasant world of FP (or semi-FP).

So what about protocols, then? Well, now that you know what kind of person you're listening to, it might make sense when I say this: protocols are *awesome*. They make *so much* sense. I can't believe we were ever doing things any other way.

Are protocols FP? Kind of. The first implementation of something protocol-like was probably in Haskell, with type classes. But OOP had a very similar system soon after, in the form of generics. And Dave Abrahams, who works on Swift, was the main guy for templates in C++ for a long time. They're not FP in the traditional sense, but they *are* FP in the sense that I understand it: they're a certain kind of style/technique. And they fit right in with the rest of the styles and techniques of FP.

# How to do it
Anyway, I should get to my strategy for using them. Here's my ridiculously oversimplified (mis)understanding of how you should see them: protocols describe *abilities* and *talents*. God that's pretentious. Lemme try again: a protocol represents something a type *can* do, and *how well* it can do it. That's a bit better.

Let's look to the standard library for our examples here. Say you want to make a method that emulates Python's slicing, where you can hop over elements of a sequence. Something like:

```scala
public extension SequenceType {
  func hop(n: Int) -> [Generator.Element] {
    var i = n - 1
    return self.filter {
      _ -> Bool in
      if ++i == n {
        i = 0
        return true
      } else {
        return false
      }
    }
  }
}
[1, 2, 3, 4, 5].hop(2) // [1, 3, 5]
```

We're in protocol-land right away: `SequenceType`{.scala}. This is an "ability". The method exists on everything with the *ability* to act like a sequence. That means arrays, sets, dictionaries, strings. Actually, a better example of the "ability" would be this:

```scala
extension IntegerArithmeticType {
  func double() -> Self {
    return self + self
  }
}

2.double() // 4
```

Goodness gracious that's contrived. But anyway, you get the idea. Anything that can do integer arithmetic gets that method.

Now, back to the hop method. Maybe it's very expensive to actually retrieve every intermediate element and then discard it - that's what filter is doing, after all. Why not just do an index lookup?

```scala
public extension CollectionType {
  func hop(n: Index.Distance) -> [Generator.Element] {
    
    var ar: [Generator.Element] = []
    
    for var i = startIndex; 
        indices.contains(i); 
        i = advance(i, n) {
          ar.append(self[i])
    }
    
    return ar
  }
}
```

There we go! Everything can *do* the hop method, but `CollectionType`{.scala}s can do it *well*. In fact, some `CollectionType`{.scala}s can do it very well indeed:

```scala
public extension CollectionType where Index : RandomAccessIndexType {  
  func hop(n: Index.Stride) -> [Generator.Element] {
    return stride(from: startIndex, to: endIndex, by: n).map{self[$0]}
  }
}
```

You see this kind of thing all around the standard library, but most prominently with the index types. If something is able to do something, it gets the bare-bones, inefficient implementation. Then, for types with all the bells and whistles, you get the clever, blazing-fast version. And to the user, all you see is some easy-looking `indexOf()`{.scala} function.

So here's how I think you should be doing your APIs: if at all possible, write your function as a method. Write the most bare-bones, slow version of it you possibly can that still makes sense. Then, specialise where it suits.

(I realise now that I may have just described a design pattern that was very obvious to everyone but me. Ah, well)

# The Why
There are pretty major advantages to this. Your two other options are generally class inheritance, or global functions with generics. [The best video from WWDC](https://developer.apple.com/videos/wwdc/2015/?id=408) talks about class inheritance, so I'll stay away from that. In contrast to global functions, here are the advantages:

## More discoverable

Hit dot after whatever thing you're interested in, and the little list of available goodies pops up. It's also easy to find in the documentation (what kind of methods do I have on sequences? vs. Right, here's the page for the global functions, cmd-f "Sequence"... hmm, `indexOf`{.scala} isn't here...)

## Function composition(ish) 

We currently have this:

```
g(f(x))
```

Now, if we were in Haskell-land, you could write:

```
(g . f) x
```

But we're not. However, if f is a method on x, and g is a method on whatever if returned by f, you can have:

```
x.f().g()
```

Maybe a bit of a bad example, but [combine that with `flatMap`{.scala} and laziness and you've got some handsome-looking, powerful functions right there.](http://airspeedvelocity.net/2015/06/23/protocol-extensions-and-the-death-of-the-pipe-forward-operator/)

## Easy-to-build hierarchies

I find myself often getting a bit philosophical around all of these protocols ("yeah, but what does it *mean* to be `IntegerLiteralConvertible`{.scala}? I mean, aren't we *all* `IntegerLiteralConvertible`{.scala}, in a way?", "Woah"). I see places where I can extend a previous method to things I hadn't even thought of applying it to. And with the quicklook, and the way the documentation is structured, none of this stuff becomes complicated.

Obviously this is a little bit of a straw man - there are some obvious cases where protocol extensions don't make a lot of sense. Having "double" as an extension on `IntegerArithmeticType`{.scala} is sheer silliness - but I think something like `sqrt()`{.scala} would be odd, as well. If only because it decreases readability, I'm not sure that those kinds of things are good ideas. At the end of the day, you're a reasonable, intelligent person, and you know where this stuff works. Just have it knocking around in your brain, so when you come across something that doesn't work *quite right*, you'll have protocol extensions as one of your other options.

If you want to see an example of protocols taken to the nth degree, the examples I've had here are taken from my library, [SwiftSequence](https://github.com/oisdk/SwiftSequence).

If you've kept reading this far, I'm going to I'm going to really test your patience with this next bit:

# What do I want?

## Beef up some of the meta-language
You know the tiny little meta-language for protocol extensions? The one that exists between the angle brackets, after the where?

```scala

extension SomeProtocol where (This bit) {...

func f<T : SomeProtocol where (This bit, also)...

```

That needs to get more powerful. Swift is big on doing loads of stuff at compile-time, and that little meta-language is effectively a script that runs as your code compiles. When it's between the angle brackets it's ugly, and it seems like too small a place for a lot of code, but if you start doing anything complex with it, you hit its limits quickly. Say you want to write a recursive function that works with slices. This is the absolute minimum in the angle brackets you need:

```scala
<  
  S : Sliceable where S.SubSlice : Sliceable,  
  S.SubSlice.Generator.Element == S.Generator.Element,  
  S.SubSlice.SubSlice == S.SubSlice  
  >
```

And if you need anything complex, well...

```scala
func bSearch<
  S : Sliceable where S.SubSlice : Sliceable,
  S.SubSlice.Generator.Element == S.Generator.Element,
  S.SubSlice.SubSlice == S.SubSlice,
  S.Generator.Element : Comparable,
  S.Index : IntegerArithmeticType,
  S.Index : IntegerLiteralConvertible,
  S.SubSlice.Index == S.Index
  >(el: S.Generator.Element, list: S) -> S.Generator.Element? {

    if list.isEmpty { return nil }

    let midInd = list.endIndex / 2

    let midEl: S.Generator.Element = list[midInd] 
    // type inference giving me some bugs here

    if midEl == el {
      return el
    }

    return midEl < el ?
      bSearch(el, list: list[midInd+1..<list.endIndex]) :
      bSearch(el, list: list[0..<midInd])
}
```

Yeah. And it's only going to get more and more complex: with every new beta, more functions become methods. This protocol business is going to cause more and more function signatures to end up looking like that. With that in mind, two things, in particular, need to go into the meta-language:

  * A way to summarise all of those protocols into one. Like, I should be able to declare a protocol that's just other protocols put together:

    ```scala
    protocol RecursiveSliceable:
      Sliceable where SubSlice : Sliceable,
      SubSlice.Generator.Element == Generator.Element,
      SubSlice.SubSlice == SubSlice
    
    protocol RecursiveSliceableIntegerIndices:
      RecursiveSliceable where
      Index : IntegerArithmeticType,
      Index : IntegerLiteralConvertible,
      SubSlice.Index == Index

    func bSearch<
      S : RecursiveSliceableIntegerIndices where
      S.Generator.Element : Comparable
      >(seq: S)...
    ```

  * Support for expressions, statements and whatnot, all of which get evaluated at compile-time.

## More POP in the Standard Library
The standard library, at the moment, still has not fully crossed over to the protocol way of doing things. It's probably more to do with resource pressure than anything else, but I'm worried that some areas may not get the full protocol treatment. I'm talking about sequences. Currently, there are structs like `AnySequence`{.scala}, which represent the old, dark days of Swift 1.2. In its description:

> A type-erased sequence.

> Forwards operations to an arbitrary underlying sequence having the same `Element` type, hiding the specifics of the underlying `SequenceType`{.scala}.

That's no good. You shouldn't have to erase types - your methods and functions should act on `SequenceType`{.scala}, regardless of which `SequenceType`{.scala} it is. I'm not suggesting you should get rid of that struct - it's trivial to come up with cases where it's needed - I'm saying you shouldn't be using it if you don't have to. And in one particular area of the Swift standard library, they use structs where (I feel) they should be using protocols: `LazySequence`{.scala}. It's a wrapper struct, mainly used for functional-style methods like `map`{.scala} and `filter`{.scala} that can act lazily. *Why isn't it a protocol*?! Currently, the lazy versions of `map`{.scala} and `filter`{.scala} are defined as methods on `LazySequence`{.scala}. What they return is a `MapSequenceView`{.scala} *wrapped* in `LazySequence`{.scala}. That way, you can chain map and filter, keeping things lazy. But why not make `LazySequenceType`{.scala} a protocol, and have `MapSequenceView`{.scala} conform to it? There's more - `LazyRandomAccessCollection`{.scala}, `LazyForwardCollection`{.scala}, etc. *These should all be protocols*. It's a nightmare to try and deal with these things: if you want to write a lazy method on a sequence, you have to write one for `LazySequence`{.scala}, then one for `LazyForwardCollection`{.scala}, and so on. It would be so much easier to have.


```scala
extension LazySequenceType where 
  Self: CollectionType, 
  Index: RandomAccessIndexType
```

I really don't know why it's not this way. Again, the Swift team may well *want* to do it, but just hasn't got round to it. I hope so. A very optimistic voice in my mind does keep whispering, though: "_they're just waiting for recursive enums, so they can introduce lazy lists... they've been working on a whole load of lazy sequence functions... pattern matching... uncons..._"
