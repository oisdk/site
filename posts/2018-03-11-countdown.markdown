---
title: Countdown
tags: Haskell
bibliography: Countdown.bib
header-includes:
- usepackage{tikz}
---

There's a popular UK TV show called [Countdown](https://en.wikipedia.org/wiki/Countdown_(game_show)) with a round where contestants have to construct an arithmetic expression from six random numbers which equals a particular target. For instance, given the numbers:

$$100,25,1,5,3,10$$

The following is a valid solution for the target 586:

$$25 * 3 + 10 + 100 * 5 + 1$$

You don't have to use all of the numbers, and you're allowed use four operations: addition, subtraction, multiplication, and division. Additionally, each stage of the calculation must result in a positive integer.

Solving it in Haskell was first explored in depth in @hutton_countdown_2002. There, a basic "generate-and-test" implementation was provided and proven correct.

As an optimization problem, there are several factors which will influence the choice of algorithm:

1. There's no obvious heuristic for constructing subexpressions in order to get to a final result. In other words, if we have $25 * 3 + 10$ and $25 * 3 * 10$, there's no easy way to tell which is "closer" to $583$. The latter is closer numerically, but the former is what we ended up using in the solution.
2. Because certain subexpressions aren't allowed, we'll be able to prune the search space as we go.
3. Ideally, we'd only want to calculate each possible subexpression once, making it a pretty standard dynamic programming problem.

I'll be focusing on the third point in this post, but we can add the second point in at the end.

## Pure Memoization

The normal way most programmers think about "memoization" is something like this:

```python
memo_dict = {0:0,1:1}

def fib(n):
    if n in memo_dict:
        return memo_dict[n]
    else:
        res = fib(n-1) + fib(n-2)
        memo_dict[n] = res
        return res
```

In other words, it's a fundamentally stateful process. We need to mutate some mapping when we haven't seen the argument before.

Using laziness, though, we can emulate the same behavior purely. Instead of mutating the mapping on function calls, we fill the whole thing at the beginning, and then index into it. As long as the mapping is lazy, it'll only evaluate the function calls when they're needed. We could use lists as our mapping to the natural numbers[^fib]:

```haskell
fibs = 0 : 1 : map fib [2..]
fib n = fibs !! (n-1) + fibs !! (n-2)
```

[^fib]: There are of course better ways to memoize the fibonacci function. My personal favourite is:

    ```haskell
    fib n = fix ((:) 0 . scanl (+) 1) !! n
    ```

In this basic form, it's worth pointing out the tradeoffs: obviously there's a memory cost, as we have to store previous results. Also, though, every memoized call has to pay the price of the lookup time in whatever mapping structure we're using. Finally, this approach will only allow us to memoize function calls with an argument that can be used as the index to some mapping: it needs to be hashable, or comparable, etc.

## Nexuses

First, let's take a quick diversion to another interesting technique that will give us another way to memoize.

To construct a binary tree full of $n$ nodes, it seems like you might have to perform (at least) $n$ operations. However, in a pure language, if we know that two branches in the tree are going to be the same, we can construct just one branch, and have the other point to it. Because no mutation will occur, the difference should be unobservable: except for performance. This is called constructing a nexus.

As described in @bird_functional_2003, we can use this idea to do perform fast memoization. The idea is that we'll make a nexus in the *call graph* of our recursive function. Taking Fibonacci again:

```haskell
                                            ┌fib(1)=1
                                   ┌fib(2)=1┤
                                   │        └fib(0)=0
                          ┌fib(3)=2┤
                          │        └fib(1)=1
                 ┌fib(4)=3┤
                 │        │        ┌fib(1)=1
                 │        └fib(2)=1┤
                 │                 └fib(0)=0
        ┌fib(5)=5┤
        │        │                 ┌fib(1)=1
        │        │        ┌fib(2)=1┤
        │        │        │        └fib(0)=0
        │        └fib(3)=2┤
        │                 └fib(1)=1
fib(6)=8┤
        │                          ┌fib(1)=1
        │                 ┌fib(2)=1┤
        │                 │        └fib(0)=0
        │        ┌fib(3)=2┤
        │        │        └fib(1)=1
        └fib(4)=3┤
                 │        ┌fib(1)=1
                 └fib(2)=1┤
                          └fib(0)=0
```

Its nexus looks like this:

```haskell
                                   ┌────────┬fib(1)=1
                 ┌────────┬fib(3)=2┤        │
        ┌fib(5)=5┤        │        │        │
fib(6)=8┤        │        │        │        │
        └────────┴fib(4)=3┤        │        │
                          └────────┴fib(2)=1┤
                                            └fib(0)=0
```

A significant advantage of this approach is that we no longer have to index using the arguments to the function: as long as the call graph stays the same, they can even be polymorphic. Also, we don't have to pay the price of indexing: chasing a pointer to the relevant node in the tree is $\mathcal{O}(1)$ (probably even cheaper than a function call).

So why don't we all use this technique? Well, firstly, it's usually easier to abstract over indexing than "call-graph shape". If I want to memoize something using hashable arguments, the memoization function might just look like:

```haskell
memo :: Hashable a => (a -> b) -> (a -> b)
```

Having programmers recognize and classify the call-graphs of their functions is a great deal more difficult: in fact, finding a good tabulation structure for a given recursive function is NP-hard in general [@steffen_table_2006]. Nonetheless, here's how you would do it for Fibonacci:

```haskell
data Tree
    = Leaf
    | Node
    { val   :: Integer
    , left  :: Tree
    , right :: Tree}

fib :: Integer -> Integer
fib = val . go
  where
    go 0 = Node 0 Leaf Leaf
    go 1 = Node 1 (Node 0 Leaf Leaf) Leaf
    go n = node t (left t) where t = go (n-1)
    node l r = Node (val l + val r) l r
```

For countdown, though, it's a great deal more complicated. 

## Hylomorphisms

A [hylomorphism](https://en.wikipedia.org/wiki/Hylomorphism_(computer_science)) is a fancy name for the pattern of algorithm that takes some input, builds up a structure using it, and then tears down that structure to compute a result. A good example is sorting using a heap: take some input list, convert it into a heap (build up), and then collapse the heap down to get the elements in order.

Put more formally, a hylomorphism is an anamorphism followed by a catamorphism. Anamorphism is the "building up" function, and catamorphism is "tearing down". For concrete examples, look no further than [`unfoldr`{.haskell}](http://hackage.haskell.org/package/base-4.10.1.0/docs/Data-List.html#v:unfoldr) and [`foldr`{.haskell}](http://hackage.haskell.org/package/base-4.10.1.0/docs/Data-List.html#v:foldr). Using these, here's a serviceable definition for a hylomorphism on lists:

```haskell
hylo :: (b -> c -> c) -> c -> (a -> Maybe (b, a)) -> a -> c
hylo f b g = foldr f b . unfoldr g
```

For a somewhat contrived example, here's how you could calculate the sum of the digits of a number:

```haskell
sumDigits :: Integer -> Integer
sumDigits = hylo (+) 0 qr
  where
    qr 0 = Nothing
    qr n = Just (swap (quotRem n 10))

>>> sumDigits 123
6

>>> sumDigits 333
9
```

That's a pretty quick intro to recursion schemes and so on, if you want something a little more in-depth I've found Jared Tobin's three articles [-@tobin_practical_2015; -@tobin_sorting_2015; -@tobin_tour_2015] on the subject to be the most readable material out there.

## Fusion and Memoization

As it happens, the function `hylo`{.haskell} above can be rewritten to not produce any intermediate list:

```haskell
hylo :: (b -> c -> c) -> c -> (a -> Maybe (b, a)) -> a -> c
hylo f b g = go where
  go = maybe b (uncurry (\x -> f x . go)) . g
```

Inlined sufficiently, the `sumDigits`{.haskell} function now becomes:

```haskell
sumDigits :: Integer -> Integer
sumDigits 0 = 0
sumDigits n =
  let (q,r) = quotRem n 10
  in r + sumDigits q
```

In this case, the version which avoids the intermediate list is obviously superior. By viewing the computation as a hylomorphism, we were able to write a more efficient version which avoids the intermediate data structure.

The question now becomes: can we go the other way? For some functions, the memoized `fib`{.haskell} above, for instance, constructing an intermediate data structure gives us a tremendous speedup. Can we rewrite other functions into a hylomorphism form to allow for memoization?

This question is the subject of @bird_hylomorphisms_2010. Unfortunately, the code in that paper has some typos in it, and I couldn't get the similar solution from @bird_functional_2003 to work either. I did finally get a working implementation of the former, which matches (as far as I can tell) the original algorithm as stated.

## The Functions

So, for Countdown, we'll need to figure out the "build up" function, and the "tear down" function. From a high-level, the tear down function will need to take two subexpressions and combine them together in all possible ways. The anamorphism, however, will need to take the list of inputs, and split it up in all possible ways. This can be accomplished with `unmerges`{.haskell}:

```haskell
unmerges [x,y] = [([x],[y])]
unmerges (x:xs) = [([x],xs)] ++ (unmerges xs >>= add x)
  where
    add x (ys,zs) = [(x:ys,zs),(ys,x:zs)]
```

It's important to recognize that this is doing *one* level of "building": it's not generating all possible combinations of all elements, it's generating all possible partitions of size 2.

So how to construct a nexus? Well, the call graph is a boolean lattice, and the spanning tree for that lattice is a binomial tree. It's pretty complex, and more understandable through code than prose, but there are two helper functions that I found interesting.

### Breadth-First Traversal

The first was a breadth-first traversal for a forest of rose trees:

```haskell
data Tree a
    = Node
    { root   :: a
    , forest :: Forest a
    }

type Forest a = [Tree a]

breadthFirst :: Forest a -> [a]
```

The obvious solution is as follows:

```haskell
breadthFirst [] = []
breadthFirst xs = map root xs ++ breadthFirst (xs >>= forest)
```

But it's not optimal: there's a `++`{.haskell}, and it constructs several unnecessary intermediate lists. The traditional way is to use a queue of some kind:

```haskell
breadthFirst = go . toQueue
  where
    go :: Queue (Tree a) -> [a]
    go xs = case uncons xs of
      Nothing -> []
      Just (Node y ys,zs) -> y : go (zs `appendList` ys)
```

A very simple queue is just a pair of lists:

```haskell
data Queue a = Queue { front :: [a], back :: [a] }

toQueue :: [a] -> Queue a
toQueue xs = Queue xs []

uncons :: Queue a -> Maybe (a, Queue a)
uncons (Queue (x:xs) ys) = Just (x, Queue xs ys)
uncons (Queue [] ys) = case reverse ys of
  [] -> Nothing
  (x:xs) -> Just (x, Queue xs [])

appendList :: Queue a -> [a] -> Queue a
appendList (Queue xs ys) zs = Queue (xs ++ reverse ys) (reverse zs)
```

It has the right asymptotics, but still performs reversals that seem unnecessary.

Another possible option would be to build the queue in one form, and traverse it in another. This makes the code simpler still:

```haskell
breadthFirst = go id
  where
    go k [] = case k [] of
      [] -> []
      xs -> go id xs
    go k (Node x xs:ys) = x : go (k . (++) xs) ys
```

We're using a difference list to build the queue. Happily, this function converts to a fold:

```haskell
breadthFirst fs = foldr go b fs id
  where
    b k = case k [] of
      [] -> []
      xs -> foldr go b xs id
    go (Node x xs) ys k = x : ys (k . (++) xs)
```

In this form, it's clear that we only need 3 things from the queue: a way to append lists, a way to check if it's empty, and a way to fold over it. We can encode this specification in the "initial" form:

```haskell
data Queue a
    = Nil
    | Queue a :++ [a]
    deriving Foldable

breadthFirst :: Forest a -> [a]
breadthFirst fs = foldr go b fs Nil
  where
    go (Node x xs) ys k = x : ys (k :++ xs)
    b Nil = []
    b xs  = foldr go b xs Nil
```

With a little help from special GHC functions, this is actually the fastest version I found:

```haskell
breadthFirst fs = foldr go b fs Nil
  where
    go (Node x xs) fw = oneShot (\bw -> x : fw (bw :++ xs))
    {-# INLINE go #-}
    b Nil         = []
    b (bw :++ st) = foldr go (foldr go b st) bw Nil
```

You can (mostly) eliminate the intermediate data structure, but you need to be able to test for an empty queue, otherwise you'll loop. Using `Maybe`{.haskell}:

```haskell
newtype Queue a = Queue
    { runQueue :: Maybe (Queue a -> Queue a) -> [a]
    }

breadthFirst :: Forest a -> [a]
breadthFirst fs = runQueue (foldr go b fs) Nothing
  where
    go (Node x xs) ys =
        Queue (\k -> let zs = fromMaybe id k . flip (foldr go) xs
                     in x : runQueue ys (Just zs))
    b = Queue (maybe [] (\xs -> runQueue (xs b) Nothing))
```

### Halving, Convolving, and Folding

One of the steps in the algorithm looks like this:

```haskell
zipFold choose empty combine =
    foldr choose empty .
    uncurry (zipWith combine) .
    first reverse .
    halve
  where
    halve xs = splitAt (length xs `div` 2) xs
```

There are four distinct steps here: first, the list is split in half, then the first half is reversed, then the two halves are zipped together, and finally the whole thing is folded using a choosing function. There are well-known tricks for doing each of these things in one pass, and we can combine them here to do all four steps in one (ish) pass. First of all, halving:

```haskell
halve xs = go xs xs
  where
    go (y:ys) (_:_:zs) = (y:ys',zs')
      where
        (ys',zs') = go ys zs
    go ys _ = ([], ys)
```

we duplicate the list, and advance one copy twice as fast as the other. When that copy hits the end, what we have in the other copy must be the second half.

We're building the second half *after* the recursive call to go, somewhat like a right fold. We can build it in reverse by using an accumulator instead:

```haskell
halveReverse xs = go [] xs xs
  where
    go k (y:ys) (_:_:zs) = go (y:k) ys zs
    go k ys _ = (k, ys)
```

`zip`{.haskell} can be written as fold:

```haskell
zip xs ys = foldr f (const []) xs ys
  where
    f x xs (y:ys) = (x,y) : xs ys
```

And, thanks to fusion laws, that means we can sub in the cons constructors in `halveReverse`{.haskell} with the `f` above:

```haskell
halveReverseZip xs' = go (const []) xs' xs'
  where
    go k (x:xs) (_:_:ys) = go (\(z:zs) -> (x,z) : k zs) xs ys
    go k ys _ = k ys
```

And finally, because *this* whole thing is being consumed by a fold, we can remove another list:

```haskell
zipFold choose empty combine xs' = go (const empty) xs' xs'
  where
    go k (x:xs) (_:_:ys) = go (\(z:zs) -> combine x z `choose` k zs) xs ys
    go k ys _ = k ys
```

<details>
<summary>
Full Code
</summary>
```haskell
import           Control.Applicative (liftA2)
import qualified Data.Tree           as Rose
import           GHC.Exts            (oneShot)

para :: (a -> [a] -> b -> b) -> b -> [a] -> b
para f b = go
  where
    go [] = b
    go (x:xs) = f x xs (go xs)

data Tree a
    = Leaf a
    | Node [Tree a]
    deriving (Show,Eq,Functor)

type Labelled a = Rose.Tree [a]

data Queue a = Nil | Queue a :++ [a]

{-# ANN module "HLint: ignore Use foldr" #-}
instance Foldable Queue where
    foldr f = go where
      go b (xs :++ ys) = go (gol b ys) xs
      go b Nil         = b
      gol b []     = b
      gol b (x:xs) = f x (gol b xs)
    {-# INLINE foldr #-}

-- | Given a nondeterministic, commutative binary operator, and a list
-- of inputs, enumerate all possible applications of the operator to
-- all inputs, without recalculating subtrees.
enumerateTrees :: (a -> a -> [a]) -> [a] -> [a]
enumerateTrees cmb (xxs :: [a]) =
    case xxs of
        [] -> []
        _  -> (extract . steps . initial) xxs
  where
    step :: [Tree (Labelled a)] -> [Tree (Labelled a)]
    step = map (fmap node) . group
    {-# INLINE step #-}

    steps :: [Tree (Labelled a)] -> [Tree (Labelled a)]
    steps xs =
        case xs of
            [_] -> xs
            _   -> steps (step xs)

    initial :: [a] -> [Tree (Labelled a)]
    initial = map (Leaf . flip Rose.Node [] . pure)
    {-# INLINE initial #-}

    extract :: [Tree (Labelled b)] -> [b]
    extract (Leaf x:_) = Rose.rootLabel x
    extract (Node ts:_) = extract ts
    extract _ = errorWithoutStackTrace "Data.SubSequences.extract: bug!"

    group :: [Tree (Labelled a)] -> [Tree [Labelled a]]
    group = para f (errorWithoutStackTrace "Data.SubSequences.group: bug!")
      where
        f _ [] _ = []
        f (Leaf x) vs a =
            Node
                [ Leaf [x, y]
                | Leaf y <- vs ] :
            a
        f (Node us) vs a = Node (zipWith comb (group us) vs) : a
        {-# INLINE f #-}

    comb :: Tree [Labelled b] -> Tree (Labelled b) -> Tree [Labelled b]
    comb (Leaf xs) (Leaf x) = Leaf (xs ++ [x])
    comb (Node us) (Node vs) = Node (zipWith comb us vs)
    comb _ _ = errorWithoutStackTrace "Data.SubSequences.comb: bug!"

    trav :: [Labelled a] -> [[a]]
    trav ts = foldr go b ts Nil
      where
        go (Rose.Node x xs) fw = oneShot (\bw -> x : fw (bw :++ xs))
        {-# INLINE go #-}
        b Nil         = []
        b (bw :++ st) = foldr go (foldr go b st) bw Nil
    {-# INLINE trav #-}

    forest :: Int -> [Labelled a] -> [Labelled a]
    forest = flip (para f (const []))
      where
        f (Rose.Node x []) t _ !_ = Rose.Node x [] : t
        f (Rose.Node x us) _ a !k =
            Rose.Node x (forest k (drop k us)) : a (k + 1)
        {-# INLINE f #-}

    node :: [Labelled a] -> Labelled a
    node ts = Rose.Node (spring (trav (forest 0 ts))) ts
      where
        spring xs = zipCombine (const []) xs xs
        zipCombine k (x:xs) (_:_:ys) =
            zipCombine
                (\case
                     (z:zs) -> concat (liftA2 cmb x z) ++ k zs
                     [] ->
                         errorWithoutStackTrace "Data.SubSequences.node: bug!")
                xs
                ys
        zipCombine k ys _ = k ys
    {-# INLINE node #-}
{-# INLINE enumerateTrees #-}
```

</details>

<details>
<summary>
Countdown Implementation
</summary>

```haskell
import Debug.SimpleReflect
import Data.Function
import qualified Data.IntSet as IntSet
data Op = Add | Dif | Mul | Div
data Memoed = Memoed { expr :: Expr, result :: Int }
binOp f g x y = Memoed ((f `on` expr) x y) ((g `on` result) x y)

apply :: Op -> Memoed -> Memoed -> Memoed
apply Add x y = binOp (+) (+) x y
apply Dif x y
  | result y < result x = binOp (-) (-) x y
  | otherwise = binOp (-) (-) y x
apply Mul x y = binOp (*) (*) x y
apply Div x y = binOp div div x y

enumerateExprs :: [Int] -> [Memoed]
enumerateExprs = enumerateTrees cmb . map (\x -> Memoed (fromIntegral x) x)
  where
    cmb x y =
        nubs $
        x :
        y :
        [ apply op x y
        | op <- [Add, Dif, Mul, Div]
        , legal op (result x) (result y) ]
    legal Add _ _ = True
    legal Dif x y = x /= y
    legal Mul _ _ = True
    legal Div x y = x `mod` y == 0
    nubs xs = foldr f (const []) xs IntSet.empty
      where
        f e a s
          | IntSet.member (result e) s = a s
          | otherwise = e : a (IntSet.insert (result e) s)

countdown :: Int -> [Int] -> [Expr]
countdown targ = map expr . filter ((==) targ . result) . enumerateExprs

>>> (mapM_ print . reduction . head) (countdown 586 [100,25,1,5,3,10])
25 * 3 + 1 + (100 * 5 + 10)
75 + 1 + (100 * 5 + 10)
76 + (100 * 5 + 10)
76 + (500 + 10)
76 + 510
586
```

</details>

## Testing the Implementation

So we've followed the paper, written the code: time to test. The specification of the function is relatively simple: calculate all applications of the commutative operator to some input, *without* recalculating subtrees.

We'll need a free structure for the "commutative operator":

```haskell
data Tree a
    = Leaf a
    | Tree a :^: Tree a
    deriving (Foldable,Eq,Ord,Show)
```

Here's the problem: it's not commutative! We can remedy it by only exporting a constructor that creates the tree in a commutative way, and we can make it a pattern synonym so it looks normal:

```haskell
{-# LANGUAGE DeriveFoldable  #-}
{-# LANGUAGE PatternSynonyms #-}

module Commutative
  (Tree(Leaf)
  ,pattern (:*:))
  where

data Tree a
    = Leaf a
    | Tree a :^: Tree a
    deriving (Eq,Ord,Show,Foldable)

pattern (:*:) :: Ord a => Tree a -> Tree a -> Tree a
pattern xs :*: ys <- xs :^: ys where
  xs :*: ys
      | xs <= ys = xs :^: ys
      | otherwise = ys :^: xs

{-# COMPLETE Leaf, (:*:) #-}
```

Now we need to check if all applications are actually tested. First, to generate all trees:

```haskell
allTrees :: Ord a => [a] -> Set (Tree a)
allTrees [x] = Set.singleton (Leaf x)
allTrees xs = Set.unions (map (uncurry f) (unmerges xs))
  where
    f ls rs = Set.fromList ((liftA2 (:*:) `on` (Set.toList . allTrees)) ls rs)

allSubTrees :: Ord a => [a] -> Set (Tree a)
allSubTrees [x] = Set.singleton (Leaf x)
allSubTrees xs =
    Set.unions (map (uncurry f . (allSubTrees *** allSubTrees)) (unmerges xs))
  where
    f ls rs =
        Set.unions
            [ls, rs, Set.fromList ((liftA2 (:*:) `on` Set.toList) ls rs)]

unmerges :: [a] -> [([a],[a])]
unmerges [x,y] = [([x],[y])]
unmerges (x:xs) =
    ([x], xs) :
    concat
        [ [(x : ys, zs), (ys, x : zs)]
        | (ys,zs) <- unmerges xs ]
unmerges _ = error "unmerges: list smaller than 2 given"
```

Then, to test:

```haskell
prop_exhaustiveSearch :: Property
prop_exhaustiveSearch =
    property $
    sized $
    \n ->
         pure $
         let src = [0 .. n]
             expect = allSubTrees src
             actual =
                 Set.fromList
                     (enumerateTrees
                          (\xs ys ->
                                [xs, ys, xs :*: ys])
                          (map Leaf src))
         in setCompare expect actual

prop_exhaustiveSearchFull :: Property
prop_exhaustiveSearchFull =
    property $
    sized $
    \n ->
         pure $
         let src = [0 .. n]
             expect = Map.fromSet (const 1) (allTrees src)
             actual =
                 freqs
                     (enumerateTrees
                          (\xs ys ->
                                [xs :*: ys])
                          (map Leaf src))
         in counterexample (mapCompare expect actual) (expect == actual)
```

And then, repeated calls:


```haskell
traceSubsequences
    :: ((Tree Int -> Tree Int -> [Tree Int]) -> [Tree Int] -> [Tree Int]) -> [Int]
    -> (Map (Tree Int) Int, [Tree Int])
traceSubsequences enm ints =
    runST $
    do ref <- newSTRef Map.empty
       let res = enm (combine ref) (map (conv ref) ints)
       traverse_ evaluate res
       intm <- readSTRef ref
       pure (intm, res)
  where
    evaluate :: Tree Int -> ST s ()
    evaluate = foldr seq (pure ())
    {-# NOINLINE evaluate #-}
    combine ref xs ys =
        unsafeRunST $
        do evaluate xs
           evaluate ys
           let zs = xs :*: ys
           modifySTRef' ref (incr zs)
           pure [zs]
    {-# NOINLINE combine #-}
    conv ref x =
        unsafeRunST $
        do let xs = Leaf x
           evaluate xs
           modifySTRef' ref (incr xs)
           pure xs
    {-# NOINLINE conv #-}
    unsafeRunST cmp = unsafePerformIO (unsafeSTToIO cmp)

prop_noRepeatedCalls :: Property
prop_noRepeatedCalls =
    property $ sized $
    \n ->
         pure $
         let src = [0 .. n]
             (tint,tres) = fmap freqs (traceSubsequences enumerateTrees src)
             (fint,fres) = fmap freqs (traceSubsequences dummyEnumerate src)
         in counterexample
                (mapCompare (freqs (allSubTrees src)) tint)
                (all (1 ==) tint) .&&.
            counterexample (mapCompare tres fres) (tres == fres) .&&.
            (n > 2 ==> tint /= fint)
```
