---
title: Convolutions and Semirings
bibliography: Semirings.bib
tags: Haskell, Semirings
---

I have been working a little more on my [semirings library](https://hackage.haskell.org/package/semiring-num) recently, and I have come across some interesting functions in the process. First, a quick recap on the `Semiring`{.haskell} class and some related functions:

```{.haskell}
class Semiring a where
  one :: a
  zero :: a
  infixl 6 <+>
  (<+>) :: a -> a -> a
  infixl 7 <.>
  (<.>) :: a -> a -> a

add :: (Foldable f, Semiring a) => f a -> a
add = foldl' (<+>) zero

mul :: (Foldable f, Semiring a) => f a -> a
mul = foldl' (<.>) one

instance Semiring Integer where
  one = 1
  zero = 0
  (<+>) = (+)
  (<.>) = (*)

instance Semiring Bool where
  one = True
  zero = False
  (<+>) = (||)
  (<.>) = (&&)
```

You can think of it as a replacement for `Num`{.haskell}, but it turns out to be much more generally useful than that.

# Matrix Multiplication

The first interesting function is to do with matrix multiplication. Here's the code for multiplying two matrices represented as nested lists:

```{.haskell}
mulMatrix :: Semiring a => [[a]] -> [[a]] -> [[a]]
mulMatrix xs ys = map (\row -> map (add . zipWith (<.>) row) cs) xs
  where
    cs = transpose ys
```

One of the issues with this code (other than its woeful performance) is that it seems needlessly list-specific. `zipWith`{.haskell} seems like the kind of thing that exists on a bunch of different structures. Indeed, the [`ZipList`{.haskell} wrapper](https://hackage.haskell.org/package/base-4.10.0.0/docs/Control-Applicative.html#t:ZipList) uses `zipWith`{.haskell} as its `<*>`{.haskell} implementation. Let's try that for now:

```{.haskell}
mulMatrix :: (Semiring a, Applicative f) => f (f a) -> f (f a) -> f (f a)
mulMatrix xs ys = fmap (\row -> fmap (add . liftA2 (<.>) row) cs) xs
  where
    cs = transpose ys
```

Of course, now `add`{.haskell} needs to work on our `f`{.haskell}, so it should be `Foldable`{.haskell}

```{.haskell}
mulMatrix 
  :: (Semiring a, Applicative f, Foldable f) 
  => f (f a) -> f (f a) -> f (f a)
mulMatrix = ...
```

`transpose`{.haskell} is the missing piece now. A little bit of `Applicative`{.haskell} magic can help us out again, though: `sequenceA`{.haskell} is `transpose`{.haskell} on `ZipList`{.haskell}s [@mcbride_applicative_2008]. 


```{.haskell}
mulMatrix 
  :: (Semiring a, Applicative f, Traversable f) 
  => f (f a) -> f (f a) -> f (f a)
mulMatrix xs ys = 
    fmap (\row -> fmap (add . liftA2 (<.>) row) cs) xs
  where
    cs = sequenceA ys
```

One further generalization: The two `f`{.haskell}s don't actually need to be the same:

```{.haskell}
mulMatrix
    :: (Applicative f, Traversable g, Applicative g, Semiring a)
    => f (g a) -> g (f a) -> f (f a)
mulMatrix xs ys = fmap (\row -> fmap (add . liftA2 (<.>) row) cs) xs
  where
    cs = sequenceA ys
```

Giving us a lovely representation of the dimensions of the two matrices. This function is present in the [linear package](https://hackage.haskell.org/package/linear-1.20.7/docs/Linear-Matrix.html#v:-33--42--33-) with some different constraints. In fairness, `Applicative`{.haskell} probably isn't the best thing to use here since it doesn't work for so many instances ([`MonadZip`{.haskell}](https://hackage.haskell.org/package/base-4.10.0.0/docs/Control-Monad-Zip.html) or something similar may be more suitable), but it's very handy to have, and works out-of the box for types like:

```{.haskell}
data Three a 
  = Three a a a 
  deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

instance Applicative Three where
  pure x = Three x x x
  Three fx fy fz <*> Three xx xy xz = Three (fx xx) (fy xy) (fz xz)
```

Which makes it (to my mind) useful enough to keep. Also, it hugely simplified the code for [matrix multiplication in square matrices](https://github.com/oisdk/Square/blob/master/src/Data/Square.hs#L183) I had, from @okasaki_fast_1999. 

# Convolutions

If you're putting a general class in a library that you want people to use, and there exist sensible instances for common Haskell types, you should probably provide those instances in the library to avoid orphans. The meaning of "sensible" here is vague: generally speaking, if there is only one obvious or clear instance, then it's sensible. For lists, the only minimal definition I could find is of polynomial multiplication. You know, where you multiply two polynomials like so:

$$(x^3 + 2x + 3)(5x + 3x^2 + 4) = 9x^5 + 15x^4 + 18x^3 + 28x^2 + 38x + 24$$

A more general definition looks something like this:

$$(a_0x^0 + a_1x^1 + a_2x^2)(b_0x^0 + b_1x^1 + b_2x^2) =$$
$$a_0b_0x^0 + (a_0b_1 + a_1b_0)x^1 + (a_0b_2 + a_1b_1 + a_2b_0)x^2 + (a_1b_2 + a_2b_1)x^3 + a_2b_2x^4$$

Or, fully generalized:

$$c_k = a_0b_k + a_1b_{k-1} + \ldots + a_{k-1}b_1 + a_kb_0$$
$$f(x) \times g(x) = \sum_{i=0}^{n+m}c_ix^i$$

So it turns out that you can represent polynomials pretty elegantly as lists. Take an example from above:

$$x^3 + 2x + 3$$

And rearrange it in order of the powers of $x$:

$$3x^0 + 2x^1 + x^3$$

And fill in missing coefficients:

$$3x^0 + 2x^1 + 0x^2 + 1x^3$$

And then the list representation of that polynomial is the list of those coefficients:

```{.haskell}
[3, 2, 0, 1]
```

For me, the definitions of multiplication above were pretty hard to understand. In Haskell, however, the definition is quite beautiful:

```{.haskell}
instance Semiring a => Semiring [a] where
  one = [one]
  zero = []
  [] <+> ys = ys
  xs <+> [] = xs
  (x:xs) <+> (y:ys) = x <+> y : (xs <+> ys)
  _ <.> [] = []
  [] <.> _ = []
  (x:xs) <.> (y:ys) = (x<.>y) : map (x<.>) ys <+> xs <.> (y:ys)
```

This definition for `<.>`{.haskell} can be found on page 4 of @mcilroy_power_1999. Although there was a version of the paper with a slightly different definition:

```{.haskell}
_ <.> [] = []
[] <.> _ = []
(x:xs) <.> (y:ys) 
  = (x<.>y) : (map (x<.>) ys <+> map (<.>y) xs <+> (zero : (xs <.> ys)))
```

Similar to one which appeared in @dolan_fun_2013.

As it happens, I prefer the first definition. It's shorter, and I figured out how to write it as a fold:

```{.haskell}
_ <.> [] = []
xs <.> ys = foldr f [] xs where
  f x zs = map (x <.>) ys <+> (zero : zs)
```

And if you inline the `<+>`{.haskell}, you get a reasonable speedup:

```{.haskell}
xs <.> ys = foldr f [] xs
  where
    f x zs = foldr (g x) id ys (zero : zs)
    g x y a (z:zs) = x <.> y <+> z : a zs
    g x y a [] = x <.> y : a []
```

The definition of `<+>`{.haskell} can also use a fold on either side for fusion purposes:

```{.haskell}
(<+>) = foldr f id where
  f x xs (y:ys) = x <+> y : xs ys
  f x xs [] = x : xs []

(<+>) = flip (foldr f id) where
  f y ys (x:xs) = x <+> y : ys xs
  f y ys [] = y : ys []
```

There are rules in the library to choose one of the above definitions if fusion is available.

This definition is much more widely useful than it may seem at first. Say, for instance, you wanted to search through pairs of things from two infinite lists. You can't use the normal way to pair things for lists, the Cartesian product, because it will diverge:

```{.haskell}
[(x,y) | x <- [1..], y <- [1..]]
-- [(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10)...
```

You'll never get beyond 1 in the first list. Zipping isn't an option either, because you won't really explore the search space, only corresponding pairs. [Brent Yorgey showed](https://byorgey.wordpress.com/2008/04/22/list-convolutions/) that if you want a list like this:

```{.haskell}
[(y,x-y) | x <- [0..], y <- [0..x] ]
-- [(0,0),(0,1),(1,0),(0,2),(1,1),(2,0),(0,3),(1,2),(2,1),(3,0)...
```

Then what you're looking for is a convolution (the same thing as polynomial multiplication). `<.>`{.haskell} above can be adapted readily:

```{.haskell}
convolve :: [a] -> [b] -> [[(a,b)]]
convolve xs ys = foldr f [] xs
  where
    f x zs = foldr (g x) id ys ([] : zs)
    g x y a (z:zs) = ((x, y) : z) : a zs
    g x y a [] = [(x, y)] : a []
```

Flatten out this result to get your ordering. This convolution is a little different from the one in the blog post. By inlining `<+>`{.haskell} we can avoid the expensive `++`{.haskell} function, without using difference lists.

# Vectors

All the hand-optimizing, inlining, and fusion magic in the world won't make a list-based implementation of convolution faster than a proper one on vectors, unfortunately. In particular, for larger vectors, a fast Fourier transform can be used. Also, usually code like this will be parallelized, rather than sequential. That said, it can be helpful to implement the slower version on vectors, in the usual indexed way, for comparison's sake:

```{.haskell}
instance Semiring a =>
         Semiring (Vector a) where
    one = Vector.singleton one
    zero = Vector.empty
    xs <+> ys =
        case compare (Vector.length xs) (Vector.length ys) of
            EQ -> Vector.zipWith (<+>) xs ys
            LT -> Vector.unsafeAccumulate (<+>) ys (Vector.indexed xs)
            GT -> Vector.unsafeAccumulate (<+>) xs (Vector.indexed ys)
    signal <.> kernel
      | Vector.null signal = Vector.empty
      | Vector.null kernel = Vector.empty
      | otherwise = Vector.generate (slen + klen - 1) f
      where
        f n =
            foldl'
                (\a k ->
                      a <+>
                      Vector.unsafeIndex signal k <.>
                      Vector.unsafeIndex kernel (n - k))
                zero
                [kmin .. kmax]
          where
            !kmin = max 0 (n - (klen - 1))
            !kmax = min n (slen - 1)
        !slen = Vector.length signal
        !klen = Vector.length kernel
```

# Search

As has been observed before [@rivas_monoids_2015] there's a pretty suggestive similarity between semirings and the `Applicative`{.haskell}/`Alternative`{.haskell} classes in Haskell:

```{.haskell}
class Semiring a where
  one :: a
  zero :: a
  (<+>) :: a -> a -> a
  (<.>) :: a -> a -> a

class Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

class Alternative f where
  empty :: f a
  (<|>) :: f a -> f a -> f a
```

So can our implementation of convolution be used to implement the methods for these classes? Partially:

```{.haskell}
newtype Search f a = Search { runSearch :: [f a] }

instance Functor f => Functor (Search f) where
  fmap f (Search xs) = Search ((fmap.fmap) f xs)

instance Alternative f => Applicative (Search f) where
  pure x = Search [pure x]
  _ <*> Search [] = Search []
  Search xs <*> Search ys = Search (foldr f [] xs) where
    f x zs = foldr (g x) id ys (empty : zs)
    g x y a (z:zs) = (x <*> y <|> z) : a zs
    g x y a [] = (x <*> y) : a []

instance Alternative f => Alternative (Search f) where
  Search xs <|> Search ys = Search (go xs ys) where
    go [] ys = ys
    go xs [] = xs
    go (x:xs) (y:ys) = (x <|> y) : go xs ys
  empty = Search []
```

At first, this seems perfect: the types all match up, and the definitions seem sensible. The issue is with the laws: `Applicative`{.haskell} and `Alternative`{.haskell} are missing *four* that semirings require. In particular: commutativity of plus, annihilation by zero, and distributivity left and right:

```{.haskell}
xs <|> ys = ys <|> xs
empty <*> xs = fs <*> empty = empty
fs <*> (xs <|> ys) = fs <*> xs <|> fs <*> ys
(fs <|> gs) <*> xs = fs <*> xs <|> gs <*> ys
```

The vast majority of the instances of `Alternative`{.haskell} today fail one or more of these laws. Taking lists as an example, `++`{.haskell} obviously isn't commutative, and `<*>`{.haskell} only distributes when it's on the right.

What's the problem, though? Polynomial multiplication follows *more* laws than those required by `Applicative`{.haskell}: why should that worry us? Unfortunately, in order for multiplication to follow those laws, it actually relies on the underlying semiring being law-abiding. And it *fails* the applicative laws when it isn't.

There are two angles from which we could come at this problem: either we relax the semiring laws and try and make our implementation of convolution rely on them as little as possible, or we find `Alternative`{.haskell} instances which follow the semiring laws. Or we could meet in the middle, relaxing the laws as much as possible until we find some `Alternative`{.haskell}s that meet our standards.

This has actually been accomplished in several papers: the previously mentioned @rivas_monoids_2015 discusses near-semirings, defined as semiring-like structures with associativity, identity, and these two laws:

$$0 \times x = 0$$
$$(x \plus y) \times z = (x \times z) \plus (y \times z)$$

In contrast to normal semirings, zero only annihilates when it's on the left, and multiplication only distributes over addition when it's on the right. Addition is not required to be commutative.

The lovely paper @spivey_algebras_2009 has a similar concept: a "bunch".

```{.haskell}
class Bunch m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
  zero :: m a
  (<|>) :: m a -> m a -> m a
  wrap :: m a -> m a
```

The laws are all the same (with `<*>`{.haskell} implemented in terms of `>>=`{.haskell}), and the extra `wrap`{.haskell} operation can be expressed like so:

```{.haskell}
wrap :: Alternative f => Search f a -> Search f a
wrap (Search xs) = Search (empty : xs)
```

A definition of `>>=`{.haskell} for our polynomials is also provided:

```{.haskell}
[] >>= _ = []
(x:xs) >>= f = foldr (<|>) empty (fmap f x) <|> wrap (xs >>= f)
```

This will require the underlying `f`{.haskell} to be `Foldable`{.haskell}. We can inline a little, and express the whole thing as a fold:

```{.haskell}
instance (Foldable f, Alternative f) => Monad (Search f) where
  Search xs >>= k = foldr f empty xs where
    f e a = foldr ((<|>) . k) (wrap a) e
```

For `Search`{.haskell} to meet the requirements of a bunch, the paper notes that the `f`{.haskell} must be assumed to be a bag, i.e., the order of its elements must be ignored.

@kiselyov_backtracking_2005 kind of goes the other direction, defining a monad which has fair disjunction and conjunction. Unfortunately, the fair conjunction loses associativity.

# Distance

The end of the paper on algebras for combinatorial search wonders if notions of distance could be added to some of the algebras. I *think* that should be as simple as supplying a suitable near-semiring for `f`{.haskell}, but the definition of `>>=`{.haskell} would need to be changed. The near-semiring I had in mind was the probability monad. It works correctly if inlined:

```{.haskell}
newtype Search s a = Search { runSearch :: [[(a,s)]] }

instance Functor (Search s) where
  fmap f (Search xs) = Search ((fmap.fmap.first) f xs)

instance Semiring s => Applicative (Search s) where
  pure x = Search [[(x,one)]]
  _ <*> Search [] = Search []
  Search xs <*> Search ys = Search (foldr f [] xs) where
    f x zs = foldr (g x) id ys (empty : zs)
    g x y a (z:zs) = (m x y ++ z) : a zs
    g x y a [] = (m x y) : a []
    m ls rs = [(l r, lp<.>rp) | (l,lp) <- ls, (r,rp) <- rs]

instance Semiring s => Alternative (Search s) where
  Search xs <|> Search ys = Search (go xs ys) where
    go [] ys = ys
    go xs [] = xs
    go (x:xs) (y:ys) = (x ++ y) : go xs ys
  empty = Search []

wrap :: Search s a -> Search s a
wrap (Search xs) = Search ([] : xs)

instance Semiring s => Monad (Search s) where
  Search xs >>= k = foldr f empty xs where
    f e a = foldr ((<|>) . uncurry (mulIn . k)) (wrap a) e
    mulIn (Search x) xp = Search ((fmap.fmap.fmap) (xp<.>) x)
```

But I couldn't figure out how to get it to work for a more generalized inner monad. The above could probably be sped up, or randomized, using the many well-known techniques for probability monad optimization.

# References
