---
title: A Very Simple Prime Sieve in Haskell
tags: Haskell
bibliography: Primes.bib
series: Prime Sieves
---

A few days ago, the [Computerphile YouTube
channel](https://www.youtube.com/user/Computerphile) put up a video about
infinite lists in Haskell [@haran_infinity_2018]. It's pretty basic, but
finishes up with a definition of an infinite list of prime numbers. The
definition was something like this:

```haskell
primes = sieve [2..]

sieve (p:ps) = p : sieve [ x | x <- ps, mod x p /= 0 ]
```

Unfortunately, and contrary to what's stated in the video, this *isn't* a
genuine [sieve of
Eratosthenes](https://en.wikipedia.org/wiki/Sieve_of_Eratosthenes). For one
thing, it uses trial division where the sieve will only use addition and
multiplication, and for another, every single new number is tested against every
previous prime (until it finds a divisor).

While obviously this isn't super important (no-one is using this algorithm to
generate primes efficiently (I hope)), it still pops up from time to time on the
internet as an example of "Haskell programmers overselling their language".
What's more, people will then point to the famous *genuine* sieve of
Eratosthenes in Haskell [@oneill_genuine_2009], and say something to the effect
of "Haskell is so difficult a simple prime sieve took a journal paper to
implement properly".

I think this is mainly silly: the example implementation is meant to showcase
how well Haskell does recursion, list processing, and lazy evaluation. What's
more, the "genuine" prime sieve is difficult not because we're working in
Haskell, but because we're working to generate *infinite primes*. The "simple"
implementation of a prime sieve in something like Python will assume a fixed
upper bound, and work with finite arrays and so on. Figuring out an efficient
implementation for an infinite prime sieve there is even *more* difficult than
it was in Haskell.

Anyway, I'm going to try today to show a very simple prime sieve that
(hopefully) rivals the simplicity of the definition above.

# A First Attempt

Visualizations of the sieve of Eratosthenes often rely on metaphors of "crossing
out" on some large table. Once you hit a prime, you cross off all of its
multiples in the rest of the table, and then you move to the next crossed-off
number.

![Sieve of Eratosthenes Animation. By Ricordisamoa, CC BY-SA 3.0, from Wikimedia
Commons](https://upload.wikimedia.org/wikipedia/commons/0/0b/Sieve_of_Eratosthenes_animation.svg)

Working with a finite array, it should be easy to see that this is extremely
efficient. You're crossing off every non-prime exactly once, only using addition
and squaring.

To extend it to infinite lists, we will use the following function:

```haskell
[] \\ ys = []
xs \\ [] = xs
(x:xs) \\ (y:ys) = case compare x y of
    LT -> x : xs \\ (y:ys)
    EQ -> xs \\ ys
    GT -> (x:xs) \\ ys
```

We're "subtracting" the right list from the left. Crucially, it works with
infinite lists:

```haskell
>>> take 10 ([1..] \\ [2,4..])
[1,3,5,7,9,11,13,15,17,19]
```

Finally, it only works if both lists are ordered and don't contain duplicates,
but our sieve does indeed satisfy that requirement. Using this, we've already
got a sieve:

```haskell
sieve (p:ps) = p : sieve (ps \\ [p*p, p*p+p..])
primes = 2 : sieve [3,5..]
```

No division, just addition and squaring, as promised. Unfortunately, though,
this doesn't have the time complexity we want. See, in the `(\\)` operation, we
have to test every entry in the sieve against the prime factor: when we're
crossing off from an array, we just jump to the next composite number.

# Using a Queue

The way we speed up the "crossing-off" section of the algorithms is by using a
priority queue: this was the optimization provided in @oneill_genuine_2009.
Before we go any further, then, let's put one together:

```haskell
infixr 5 :-
data Queue a b = Queue
    { minKey :: !a
    , minVal :: b
    , rest   :: List a b
    }

data List a b
    = Nil
    | (:-) {-# UNPACK #-} !(Queue a b)
           (List a b)


(<+>) :: Ord a => Queue a b -> Queue a b -> Queue a b
(<+>) q1@(Queue x1 y1 ts1) q2@(Queue x2 y2 ts2)
  | x1 <= x2 = Queue x1 y1 (q2 :- ts1)
  | otherwise = Queue x2 y2 (q1 :- ts2)

mergeQs :: Ord a => List a b -> Queue a b
mergeQs (t :- Nil)        = t
mergeQs (t1 :- t2 :- Nil) = t1 <+> t2
mergeQs (t1 :- t2 :- ts)  = (t1 <+> t2) <+> mergeQs ts
mergeQs Nil               = errorWithoutStackTrace "tried to merge empty list"

insert :: Ord a => a -> b -> Queue a b -> Queue a b
insert !k !v = (<+>) (singleton k v)

singleton :: a -> b -> Queue a b
singleton !k !v = Queue k v Nil
```

These are pairing heaps: I'm using them here because they're relatively simple
and very fast. A lot of their speed comes from the fact that the top-level
constructor (`Queue`) is *non-empty*. Since, in this algorithm, we're only
actually going to be working with non-empty queues, this saves us a pattern
match on pretty much every function. They're also what's used in [Data.Sequence
for
sorting](https://github.com/haskell/containers/blob/master/Data/Sequence/Internal/sorting.md#sorting).

With that, we can write our proper sieve:

```haskell
insertPrime x xs = insert (x*x) (map (*x) xs)

adjust x q@(Queue y (z:zs) qs)
  | y <= x = adjust x (insert z zs (mergeQs qs))
  | otherwise = q

sieve (x:xs) = x : sieve' xs (singleton (x*x) (map (*x) xs))
  where
    sieve' (x:xs) table
      | minKey table <= x = sieve' xs (adjust x table)
      | otherwise = x : sieve' xs (insertPrime x xs table)
      
primes = 2 : sieve [3,5..]
```

# Simplifying

The priority queue stores lists alongside their keys: what you might notice is
that those lists are simply sequences of the type $[x, 2x, 3x, 4x...]$ and so
on. Rather than storing the whole list, we can instead store just the head and
the step. This also simplifies (and greatly speeds up) the expensive `map (*x)`
operation to just *two* multiplications. If you wanted, you could just sub in
this representation of streams for all the lists above:

```haskell
data Stepper a = Stepper { start :: a, step :: a }

nextStep :: Num a => Stepper a -> (a, Stepper a)
nextStep (Stepper x y) = (x, Stepper (x+y) y)

pattern x :- xs <- (nextStep -> (x,xs))

(^*) :: Num a => Stepper a -> a -> Stepper a
Stepper x y ^* f = Stepper (x * f) (y * f)
```

If you were so inclined, you could even make it conform to `Foldable`:

```haskell
data Stepper a where
    Stepper :: Num a => a -> a -> Stepper a

nextStep (Stepper x y) = (x, Stepper (x+y) y)

pattern x :- xs <- (nextStep -> (x,xs))

instance Foldable Stepper where
    foldr f b (x :- xs) = f x (foldr f b xs)
```

But that's overkill for what we need here.

Second observation is that if we remove the wheel (from 2), the "start" is
simply the *key* in the priority queue, again cutting down on space.

Finally, we get the implementation:

```haskell
primes = 2 : sieve 3 (singleton 4 2)
  where
    adjust x q@(Queue y z qs)
        | x < y = q
        | otherwise = adjust x (insert (y + z) z (mergeQs qs))
    sieve x q
        | x < minKey q = x : sieve (x + 1) (insert (x * x) x q)
        | otherwise = sieve (x + 1) (adjust x q)
```

8 lines for a lazy prime sieve isn't bad!

I haven't tried a huge amount to optimize the function, but it might be worth
looking in to how to add back the wheels. I noticed that for no wheels, the
queue contains only two elements per key; for one (the 2 wheel), we needed 3. I
wonder if this pattern continues: possibly we could represent wheels as finite
lists at each key in the queue. Maybe in a later post.
