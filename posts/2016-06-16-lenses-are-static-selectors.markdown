---
title: Lenses are Static Selectors
tags: Swift
---

So I don't really know what [KVC](https://developer.apple.com/library/mac/documentation/Cocoa/Conceptual/KeyValueCoding/Articles/KeyValueCoding.html) is, or much about `performSelector`{.scala} functions. [This](http://inessential.com/2016/05/20/updating_local_objects_with_server_objec) blogpost, from Brent Simmons, let me know a little bit about why I would want to use them.

It centred around removing code repetition of this type:
```scala
if localObject.foo != serverObject.foo {
  localObject.foo = serverObject.foo
}

if localObject.bar != serverObject.bar {
  localObject.bar = serverObject.bar // There was an (intentional)
}                                    // bug here in the original post
```
To clean up the code, Brent used selector methods. At first, I was a little uncomfortable with the solution. As far as I could tell, the basis of a lot of this machinery used functions with types like this:
```scala
func get(fromSelector: String) -> AnyObject?
func set(forSelector: String) -> ()
```
Which *seems* to be extremely dynamic. Stringly-typed and all that. Except that there are two different things going on here. One is the dynamic stuff; the ability to get rid of types when you need to. The other, though, has *nothing* to do with types. The other idea is being able to pass around something which can access the property (or method) of an object.
Let's look at the code that was being repeated:
```scala
if localObject.foo != serverObject.foo {
  localObject.foo = serverObject.foo
}

if localObject.bar != serverObject.bar {
  localObject.bar = serverObject.bar
}
```
The logical, obvious thing to do here is try refactor out the common elements. In fact, the only things that *differ* between the two actions above are the `foo`{.scala} and `bar`{.scala}. It would be great to be able to write a function like this:
```scala
func checkThenUpdate(selector) {
  if localObject.selector != serverObject.selector {
    localObject.selector = serverObject.selector
  }
}
```
And then maybe a single line like this:
```scala
[foo, bar, baz].forEach(checkThenUpdate)
```
That's pretty obviously better. It's just good programming: when faced with repetition, find the repeated part, and abstract it out. Is it more *dynamic* than the repetition, though? I don't think so. All you have to figure out is an appropriate type for the selector, and you can keep all of your static checking. To me, it seems a lot like a [lens](https://hackage.haskell.org/package/lens):
```scala
struct Lens<Whole, Part> {
  let get: Whole -> Part
  let set: (Whole, Part) -> Whole
}
```
(This is a lens similar to the ones used in the [data-lens](http://hackage.haskell.org/package/data-lens) library, in contrast to van Laarhoven lenses, or LensFamilies. LensFamilies are used in the [lens](https://hackage.haskell.org/package/lens) package, and they allow you to change the type of the `Part`{.scala}. They're also just normal functions, rather than a separate type, so you can manipulate them in a pretty standard way. Swift's type system isn't able to model those lenses, though, unfortunately.)
It has two things: a getter and a setter. The getter is pretty obvious: it takes the object, and returns the property. The setter is a little more confusing. It's taking an object, and the new property you want to stick in to the object, and returns the object with that property updated.
For instance, if we were to make a `Person`{.scala}:
```scala
struct LocalPerson {
  var age: Int
  var name: String
}
```
We could then have a lens for the `name`{.scala} field like this:
```scala
let localName: Lens<LocalPerson,String> = Lens(
  get: { p in p.name },
  set: { (oldPerson,newName) in
    var newPerson = oldPerson
    newPerson.name = newName
    return newPerson
  }
)
```
And you'd use it like this:
```scala
let caoimhe = LocalPerson(age: 46, name: "caoimhe")
localName.get(caoimhe) // 46
localName.set(caoimhe, "breifne") // LocalPerson(age: 46, name: "breifne")
```
Straight away, we're able to do (something) like the `checkThenUpdate`{.scala} function:
```scala
func checkThenUpdate
  <A: Equatable>
  (localLens: Lens<LocalPerson,A>, serverLens: Lens<ServerPerson,A>) {
  let serverProp = serverLens.get(serverObject)
  if localLens.get(localObject) != serverProp {
    localObject = localLens.set(localObject,serverProp)
  }
}
```
And it could be called pretty tersely:
```scala
checkThenUpdate(localName, serverLens: serverName)
```
The biggest problem with this approach, obviously, is the boilerplate. In Haskell, that's solved with Template Haskell, so the lens code is generated for you. (I'd love to see something like that in Swift)
There's a protocol-oriented spin on lenses, also. One of the variants on lenses in Haskell are called "classy-lenses". That's where, instead of just generating a lens with the same name as the field it looks into, you generate a typeclass (protocol) for anything with that lens. In Swift, it might work something like this:
```scala
struct Place {
  var name: String
}

// Instead of just having a lens for the name field, have a whole protocol
// for things with a name field:

protocol HasName {
  associatedtype Name
  static var name: Lens<Self,Name> { get }
  var name: Name { get set }
}

// Because the mutable property is included in the protocol, you can rely on
// it in extensions:

extension HasName {
  static var name: Lens<Self,Name> {
    return Lens(
      get: {$0.name},
      set: { (w,p) in 
        var n = w
        n.name = p
        return n
      }
    )
  }
  var name: Name {
    get { return Self.name.get(self) }
    set { self = Self.name.set(self,newValue) }
  }
}

// This way, you can provide either the lens or the property, and you get the
// other for free.

extension Place: HasName {}

// Then, you can rely on that protocol, and all of the types:

func checkEqualOnNames
  <A,B where A: HasName, B: HasName, A.Name: Equatable, A.Name == B.Name>
  (x: A, _ y: B) -> Bool {
    return x.name == y.name
}
```
This protocol lets you do a kind of static `respondsToSelector`{.scala}, with all of the types intact.
Other people have spoken about the other things you can do with lenses in Swift ([Brandon Williams - Lenses in Swift](https://www.youtube.com/watch?v=ofjehH9f-CU)), like composing them together, chaining operations, etc. (One other thing they can emulate is [method cascading](https://gist.github.com/erica/6794d48d917e2084d6ed)) Unfortunately, in current Swift, the boilerplate makes all of this a little unpleasant. Still, they're an interesting idea, and they show how a good type system needn't always get in the way.
