---
title: Countdown
tags: Haskell
bibliography: Countdown.bib
header-includes:
- usepackage{tikz}
---

There's a popular UK TV show called [Countdown](https://en.wikipedia.org/wiki/Countdown_(game_show)) with a round where contestants have to construct an arithmetic expression from six random numbers which equals a particular target.

You don't have to use all of the numbers, and you're allowed use four operations: addition, subtraction, multiplication, and division. Additionally, each stage of the calculation must result in a positive integer.

Here's an example. Try get to the target 586:

$$100,25,1,5,3,10$$

On the show, contestants get 30 seconds to think of an answer.

<details>
<summary>
Solution
</summary>
$$25 * 3 + 10 + 100 * 5 + 1$$
</details>

Solving it in Haskell was first explored in depth in @hutton_countdown_2002. There, a basic "generate-and-test" implementation was provided and proven correct.

As an optimization problem, there are several factors which will influence the choice of algorithm:

1. There's no obvious heuristic for constructing subexpressions in order to get to a final result. In other words, if we have $25 * 3 + 10$ and $25 * 3 * 10$, there's no easy way to tell which is "closer" to $586$. The latter is closer numerically, but the former is what we ended up using in the solution.
2. Because certain subexpressions aren't allowed, we'll be able to prune the search space as we go.
3. Ideally, we'd only want to calculate each possible subexpression once, making it a pretty standard dynamic programming problem.

I'll be focusing on the third point in this post, but we can add the second point in at the end. First, however, let's write a naive implementation.

## Generating all Expressions

The simplest implementation I can think of is one which generates all possible expressions from the input, and then tests each one successively. The core function we'll use for this is usually referred to as "unmerges":

```haskell
unmerges [x,y] = [([x],[y])]
unmerges (x:xs) =
    ([x],xs) :
    concat
        [ [(x:ys,zs),(ys,x:zs)]
        | (ys,zs) <- unmerges xs ]
unmerges _ = []
```

It generates all possible 2-partitions of a list, ignoring order:

```haskell
>>> unmerges "abc"
[("a","bc"),("ab","c"),("b","ac")]
```

I haven't looked much into how to optimize this function or make it nicer, as we'll be swapping it out later.

Next, we need to make the recursive calls:

```haskell
allExprs :: (a -> a -> [a]) -> [a] -> [a]
allExprs _ [x] = [x]
allExprs c xs =
    [ e
    | (ys,zs) <- unmerges xs
    , y <- allExprs c ys
    , z <- allExprs c zs
    , e <- c y z ]
```

Finally, using the [simple-reflect](https://hackage.haskell.org/package/simple-reflect) library, we can take a look at the output:

```haskell
>>> allExprs (\x y -> [x+y,x*y]) [1,2] :: [Expr]
[1 + 2,1 * 2]
>>> allExprs (\x y -> [x+y]) [1,2,3] :: [Expr]
[1 + (2 + 3),1 + 2 + 3,2 + (1 + 3)]
```

Even at this early stage, we can actually already write a rudimentary solution:

```haskell
countdown :: [Integer] -> Integer -> [Expr]
countdown xs targ =
    filter
        ((==) targ . toInteger)
        (allExprs
             (\x y -> [x,y,x+y,x*y])
             (map fromInteger xs))

>>> mapM_ print (countdown [100,25,1,5,3,10] 586)
1 + (100 * 5 + (25 * 3 + 10))
1 + (100 * 5 + 25 * 3 + 10)
1 + (25 * 3 + (100 * 5 + 10))
1 + 100 * 5 + (25 * 3 + 10)
100 * 5 + (1 + (25 * 3 + 10))
100 * 5 + (1 + 25 * 3 + 10)
100 * 5 + (25 * 3 + (1 + 10))
1 + (100 * 5 + 25 * 3) + 10
1 + 100 * 5 + 25 * 3 + 10
100 * 5 + (1 + 25 * 3) + 10
100 * 5 + 25 * 3 + (1 + 10)
1 + 25 * 3 + (100 * 5 + 10)
25 * 3 + (1 + (100 * 5 + 10))
25 * 3 + (1 + 100 * 5 + 10)
25 * 3 + (100 * 5 + (1 + 10))
```

As you can see from the output, there's a lot of repetition. We'll need to do some memoization to speed it up.

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

Using laziness, though, we can emulate the same behavior purely. Instead of mutating the mapping on function calls, we fill the whole thing at the beginning, and then index into it. As long as the mapping is lazy, it'll only evaluate the function calls when they're needed. We could use lists as our mapping to the natural numbers:

```haskell
fibs = 0 : 1 : map fib [2..]
fib n = fibs !! (n-1) + fibs !! (n-2)
```


The benefit here is that we avoid the extra work of redundant calls. However, we pay for the speedup in three ways:

(@space) Space: we need to take up memory space storing the cached solutions.
(@indexing) Indexing: while we no longer have to pay for the expensive recursive calls, we *do* now have to pay for indexing into the data structure. In this example, we're paying linear time to index into the list.
(@generality) Generality: the memoization is tied directly to the argument type to the function. We need to be able to use the argument to our memoized function as an index into some data structure. While a lot of argument types admit some type of indexing (whether they're `Hashable`{.haskell}, `Ord`{.haskell}, etc.), some don't, and we can't memoize those using this technique.

We're going to look at a technique that allow us to somewhat mitigate @indexing and @generality above, using something called a *nexus*.

## Nexuses

The standard technique of memoization is focused on the arguments to the function, creating a concrete representation of them in memory to map to the results. Using nexuses, as described in @bird_functional_2003, we'll instead focus on the function itself, creating a concrete representation of its call graph in memory. Here's the call graph of Fibonacci:

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

Turning *that* into a concrete datatype wouldn't do us much good: it still has the massively redundant computations in it. However, we can recognize that entire subtrees are duplicates of each other: in those cases, instead of creating both subtrees, we could just create one and have each parent point to it[^fib]:

[^fib]: If you think that structure looks more like a funny linked list than a tree, that's because it is. Instead of talking about "left" and "right" branches, we could talk about the first and second elements in a list: in fact, this is exactly what's happening in the famous `zipWith`{.haskell} Fibonacci implementation (in reverse).

    ```haskell
    fibs = 0 : 1 : zipWith (+) fibs (tail fibs)
    ```
    
    Or, in my favourite version:

    ```haskell
    fib n = fix ((:) 0 . scanl (+) 1) !! n
    ```

```haskell
                                   ┌────────┬fib(1)=1
                 ┌────────┬fib(3)=2┤        │
        ┌fib(5)=5┤        │        │        │
fib(6)=8┤        │        │        │        │
        └────────┴fib(4)=3┤        │        │
                          └────────┴fib(2)=1┤
                                            └fib(0)=0
```

This is a nexus. In Haskell, it's not observably different from the other form, except that it takes up significantly less space. It's also much quicker to construct.

If we use it to memoize `fib`{.haskell}, we'll no longer be indexing on the argument: we'll instead follow the relevant branch in the tree to the subcomputation, which is just chasing a pointer. It also means the argument doesn't have to be constrained to any specific type. Here's how you'd do it:

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

So this approach sounds amazing, right? No constraints on the argument type, no need to pay for indexing: why doesn't everyone use it everywhere? The main reason is that figuring out a nexus for the call-graph is *hard*. In fact, finding an optimal one is NP-hard in general [@steffen_table_2006].

The second problem is that it's difficult to abstract out. The standard technique of memoization relies on building a mapping from keys to values: about as bread-and-butter as it gets in programming. Even more, we already know how to say "values of this type can be used efficiently as keys in some mapping": for Data.Map it's `Ord`{.haskell}, for Data.HashMap it's `Hashable`{.haskell}. All of this together means we can build a nice library for memoization which exports the two following functions:

```haskell
memoHash :: Hashable a => (a -> b) -> (a -> b)
memoOrd :: Ord a => (a -> b) -> (a -> b)
```

Building a nexus, however, is not bread-and-butter. On top of that, it's difficult to say something like "recursive functions of this structure can be constructed using a nexus". What's the typeclass for that? In comparison to the signatures above, the constraint will need to be on the *arrows*, not the `a`{.haskell}. Even talking about the structure of recursive functions is regarded as somewhat of an advanced subject: that said, the [recursion-schemes](https://hackage.haskell.org/package/recursion-schemes) package allows us to do so, and even has facilities for constructing something *like* nexuses with histomorphisms [@tobin_time_2016]. I'm still looking to see if there's a library out there that *does* manage to abstract nexuses in an ergonomic way, so I'd love to hear if there was one (or if there's some more generalized form which accomplishes the same).

## Memoizing Countdown

That's enough preamble. The nexus we want to construct for countdown is *not* going to memoize as much as possible: in particular, we're only going to memoize the shape of the trees, not the operators used. This will massively reduce the memory overhead, and still give a decent speedup.

With that in mind, the ideal nexus looks something like this:

![](/images/boolean-lattice.svg)

We can represent the tree in Haskell as a rose tree:

```haskell
data Tree a
    = Node
    { root   :: a
    , forest :: Forest a
    }

type Forest a = [Tree a]
```

Constructing the nexus itself isn't actually the most interesting part of this solution: *consuming* it is. We need to be able to go from the structure above into a list that's the equivalent of `unmerges`{.haskell}. Doing a breadth-first traversal of the diagram above (without the top element) will give us:

$$abc, abd, acd, bcd, ab, ac, bc, ad, bd, cd, a, b, c, d$$

If you split that list in half, and zip it with its reverse, you'll get the output of `unmerges`{.haskell}.

However, the breadth-first traversal of the diagram isn't the same thing as the breadth-first traversal of the rose tree. The latter will traverse $abc, abd, acd, bcd$, and then the children of $abc$ ($ab,ac,bc$), and then the children of $abd$ ($ab,ad,bd$): and here's our problem. We traverse $ab$ twice, because we can't know that $abc$ and $abd$ are pointing to the same value. What we have to do is first prune the tree, removing duplicates, and then perform a breadth-first traversal on that.

### Pruning

Luckily, the duplicates follow a pattern, allowing us to remove them without having to do any equality checking. In each row, the first node has no duplicates in its children, the second's first child is a duplicate, the third's first and second children are duplicates, and so on. You should be able to see this in the diagram above. Adapting a little from the paper, we get an algorithm like this:

```haskell
para :: (a -> [a] -> b -> b) -> b -> [a] -> b
para f b = go
  where
    go [] = b
    go (x:xs) = f x xs (go xs)

prune :: Forest a -> Forest a
prune ts = pruneAt ts 0 
  where
    pruneAt = para f (const [])
    f (Node x []) t _ _ = Node x [] : t
    f (Node x us) _ a k =
        Node x (pruneAt (drop k us) k) : a (k + 1)
```

### Breadth-First Traversal

The obvious solution is as follows:

```haskell
breadthFirst [] = []
breadthFirst xs = map root xs ++ breadthFirst (xs >>= forest)
```

But it's not optimal: there's a `++`{.haskell}, and it constructs several unnecessary intermediate lists. The traditional way is to use a queue of some kind, but you can actually get away with just a list and a left fold.

```haskell
breadthFirst :: Forest a -> [a]
breadthFirst ts = foldr f b ts []
  where
    f (Node x xs) fw bw = x : fw (xs:bw)

    b [] = []
    b q = foldl (foldr f) b q []
```

With the appropriate incantations, this is actually the fastest implementation I've found.

### Fusing

We can actually inline both of the above functions, fusing them together:

```haskell
spanNexus :: Forest a -> [a]
spanNexus ts = foldr f (const b) ts 0 []
  where
    f (Node x us) fw k bw = x : fw (k+1) ((k, us) : bw)

    b [] = []
    b q = foldl (\a (k,st) -> foldr f (const a) (drop k st) k) b q []
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
