---
title: Recursion Schemes Examples
tags: Haskell
bibliography: Recursion Schemes.bib
---
```{.haskell .literate .hidden_source}
{-# LANGUAGE LambdaCase #-}

module RecSchemes where
```

Recursion schemes are a reasonably advanced topic in functional programming: they've got names like "catamorphism", and a lot of the information out there is contained in academic papers [including the original, @meijer_functional_1991]. Beyond the most basic schemes, they're not necessarily that useful. That said, they're extremely interesting! So I thought I'd go through a few examples of them.

There's a [whole](http://blog.sumtypeofway.com/an-introduction-to-recursion-schemes/) [bunch](https://medium.com/@jaredtobin/practical-recursion-schemes-c10648ec1c29#.8hoj0epkx) of blog posts out there on recursion schemes (there may be a danger of it becoming the new [monad tutorial](https://wiki.haskell.org/Monad_tutorials_timeline)). However, the best [field guide](http://comonad.com/reader/2009/recursion-schemes/) doesn't provide code examples, and I couldn't understand it the first time I read it, hence this post.

I'm going to use the [recursion-schemes](https://hackage.haskell.org/package/recursion-schemes) package throughout this post.

# Catamorphisms

This is the first, and most familiar, recursion scheme. The "cata" prefix indicates breaking down (think catastrophe), and "morphism" indicates transformation (all of the recursion schemes are suffixed by "morphism").

To see an example, let's define a tree:

```{.haskell .literate}
data Tree a = Leaf | Node (Tree a) a (Tree a)
```

To sum up each element in the tree, you could write a recursive function like this:

```{.haskell .literate}
recSum :: Num a => Tree a -> a
recSum Leaf = 0
recSum (Node ls x rs) = recSum ls + x + recSum rs
```

If the tree is a binary search tree, then finding whether or not an element is present might look like this:

```{.haskell .literate}
recIsElement :: Ord a => a -> Tree a -> Bool
recIsElement x = go where
  go Leaf = False
  go (Node ls y rs) = case compare x y of
    LT -> go ls
    EQ -> True
    GT -> go rs
```

Here's the question, then: how to factor out the recursion? These examples are different enough that we can't stick in a `deriving Foldable`{.haskell} and formulate each as a (simple) fold. The recursion is a little more involved.

The solution used by the recursion-schemes library is to make a separate type with *holes* where the recursive calls would go. By convention, this type has `F`{.haskell} as a suffix:

```{.haskell .literate}
data TreeF a rec = LeafF | NodeF r a r
```

We need to indicate that this is the "holed" type of `Tree`{.haskell}, with a type family:

```{.haskell .literate}
type instance Base (Tree a) = TreeF a
```

The combinators need to know where the holes are:

```{.haskell .literate}
instance Functor (TreeF a) where
  fmap f LeafF = LeafF
  fmap f (NodeF l x r) = NodeF (f l) x (f r)
```

Then, we need to be able to go from one type to the other:

```{.haskell .literate}
instance Recursive (Tree a) where
  project Leaf = LeafF
  project (Node l x r) = NodeF l x r
```

Then finally, time for the catamorphism:

```{.haskell .literate}
cataSum :: Num a => Tree a -> a
cataSum = cata $ \case
  LeafF -> 0
  NodeF l x r -> l + x + r

cataFind :: Ord a => a -> Tree a -> Bool
cataFind x = cata $ \case
  LeafF -> False
  NodeF l y r -> case compare x y of
    LT -> l
    EQ -> True
    GT -> r
```

 (I'm using `-XLambdaCase` here)
 
Handy!

# Zygomorphisms

Usually at this point, people mention paramorphisms, but (I think) zygomorphisms are more foundational, so I thought I'd talk about them first. 

Here's the problem: you want to find out whether or not your tree is balanced. You write an algebra for finding the height of the tree:

```{.haskell .literate}
heightAlg :: TreeF a Integer -> Integer
heightAlg LeafF = 0
heightAlg (NodeF ls _ rs) = max ls rs + 1
```

You can get this to give you the height no problem:

```{.haskell .literate}
cataHeight :: Tree a -> Integer
cataHeight = cata heightAlg
```

But balance is more complex. Here's the version with explicit recursion:

```{.haskell .literate}
balancedRec :: Tree a -> Bool
balancedRec LeafF = True
balancedRec (Node ls _ rs) 
  = balancedRec ls 
  && balancedRec rs 
  && cataHeight ls == cataHeight rs
```

The issue is that *two* algebras need to be called at once. In the version above, `cataHeight` is called unnecessarily a bunch of times, and threading the height measures through for efficiency's sake sounds like a headache. This is what `zygo` is for [@hinze_unifying_2013]:

```{.haskell .literate}
balancedZygo :: Tree a -> Bool
balancedZygo = zygo heightAlg $ \case
  LeafF -> True
  NodeF (lh,lb) _ (rh,rb) -> lb && rb && lh == rh
```

# Paramorphisms

Paramorphisms are kind of like zygomorphisms, in that they give you access to two pieces of information at once while you recurse. However, the extra piece of information is actually a copy of the structure you're recursing over at the point of recursion. Here's an example (from [here](http://stackoverflow.com/questions/13317242/what-are-paramorphisms)):

```{.haskell .literate}
insert :: Ord a => a -> Tree a -> Tree a
insert x = para $ \case
  LeafF -> Node Leaf x Leaf
  NodeF (ln,li) y (rn,ri) -> case compare x y of
    LT -> Node li y rn
    EQ -> Node ln y rn
    GT -> Node ln y ri
```

# Anamorphisms

