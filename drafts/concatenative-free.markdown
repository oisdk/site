---
title: Concatenative Programming; The Free Monoid of Programming Languages
tags: Concatenative
---


Point-free style is one of the distinctive markers of functional programming
languages.
Want to sum a list?
That's as easy as:

```haskell
sum = foldr (+) 0
```

Now I want to sum every number after adding one to it.

```haskell
sumSuccs = foldr (+) 0 . map ((+) 1)
```

One more step to make this function truly abstract™ and general™: we'll allow
the user to supply their own number to add

```haskell
sumAdded = foldr (+) 0 . map . (+)
```

And here the trouble begins.
The above expression won't actually type check.
In fact, it'll give a pretty terrible error message:

```
• Non type-variable argument in the constraint: Num [a]
  (Use FlexibleContexts to permit this)
• When checking the inferred type
    sumThoseThat :: forall a.
                    (Num [a], Foldable ((->) [a])) =>
                    a -> [a]
```

I remember as a beginner being confused by similar messages.
What's `FlexibleContexts`?
I had thought that the "point-free style" just meant removing the last variable
from an expression if it's also the last argument:

```haskell
sum xs = foldr (+) 0 xs
sum = foldr (+) 0
```

Why doesn't it work here?

Well, it doesn't work because the types don't line up, but I'm going to try and
explain a slightly different perspective on the problem, which is
*associativity*.

To make it a little clearer, let's see
what happens when we point-fill the expression:

```haskell
sumAdded n xs = (foldr(+) 0 . (map . (+))) n xs
             => foldr(+) 0 ((map . (+)) n) xs
             => foldr(+) 0 (map ((+) n)) xs
```

Indeed, the problem is the placement of the parentheses.
What we want at the end is:
```haskell
             => foldr(+) 0 (map ((+) n) xs)
```

But, no matter.
We have to jiggle the arguments around, or we could use something terrible like
this:

```haskell
infixr 9 .:
(.:) = (.).(.)

sumAdded = foldr (+) 0 .: map . (+)
```

Is there something, though, that could do this automatically?

# Associativity

We run into a similar problem in Agda.
We're forever having to prove statements like:

```agda
(x + y) + z ≡ x + (y + z)
x ≡ x + 0
```

There are a couple of ways to get around the issue, and for monoids there's a
rich theory of techniques.
I'll just show one for now, which relies on the *endomorphism* monoid.
This monoid is created by partially applying the monoid's binary operator:

```agda
Endo : Set
Endo = ℕ → ℕ

⟦_⇑⟧ : ℕ → Endo
⟦ n ⇑⟧ m = n + m
```

And you can get back to the underlying monoid by applying it to the neutral
element:

```agda
⟦_⇓⟧ : Endo → ℕ
⟦ n ⇓⟧ = n 0
```

Here's the important parts: first, we can lift the underlying operation into the
endomorphism:

```agda
_⊕_ : Endo → Endo → Endo
xs ⊕ ys = λ x → xs (ys x)

⊕-homo : ∀ n m → ⟦ ⟦ n ⇑⟧ ⊕ ⟦ m ⇑⟧ ⇓⟧ ≡ n + m
⊕-homo n m = cong (n +_) (+-identityʳ m)
```

And second, it's *definitionally* associative.

```agda
⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
⊕-assoc _ _ _ = refl
```

These are all clues as to how to solve the composition problem in the Haskell
code above.
We need definitional associativity, somehow.
Maybe we can get it from the endomorphism monoid?

# State

You're probably familiar with Haskell's state monad:

```haskell
newtype State s a = State { runState :: s -> (a, s) }
```

It can help a lot when you're threading around fiddly accumulators and so on.

```haskell
nub :: Ord a => [a] -> [a]
nub = go Set.empty
  where
    go seen [] = []
    go seen (x:xs)
      | x `Set.member` seen = go seen xs
      | otherwise = x : go (Set.insert x seen) xs
```

```haskell
nub :: Ord a => [a] -> [a]
nub = flip evalState Set.empty . go
  where
    go [] = pure []
    go (x:xs) = do
        seen <- gets (Set.member x)
        if seen
          then go xs
          else do
              modify (Set.insert x)
              (x:) <$> go xs
```

Of course, these days state is a transformer:

```haskell
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }
```

This lets us stack multiple effects on top of each other: error handling, IO,
randomness, even another state monad.
In fact, if you *do* stack another state monad on top, you might be surprised by
the efficiency of the code it generates:

```haskell
type DoubleState s1 s2 a = StateT s1 (State s2) a
                        => s1 -> State s2 (a, s1)
                        => s1 -> s2 -> ((a, s1), s2)
```

It's nothing earth shattering, but it inlines and optimises well.
That output is effectively a left-nested list, also.

# Multi-State

If we can do one, and we can do two, why not more?
Can we generalise the state pattern to an arbitrary number of variables?
First we'll need a generic tuple:

```haskell
infixr 5 :-
data Stack (xs :: [Type]) :: Type where
    Nil  :: Stack '[]
    (:-) :: x -> Stack xs -> Stack (x : xs)
```

Then, the state type.

```haskell
newtype State xs a = State { runState :: Stack xs -> (a, Stack xs) }
```

We can actually clean the definition up a little: instead of a tuple at the
other end, why not push it onto the stack.

```haskell
newtype State xs a = State { runState :: Stack xs -> Stack (a : xs) }
```

In fact, let's make this as polymorphic as possible.
We should be able to change the state is we so desire.

```haskell
infixr 0 :->
type (:->) xs ys = Stack xs -> Stack ys
```

We can, of course, get back our original types.

```haskell
newtype State xs a = State { runState :: xs :-> a : xs }
```

And it comes with all of the instances you might expect:

```haskell
instance Functor (State xs) where
    fmap f xs = State (\s -> case runState xs s of
        (x :- ys) -> f x :- ys)
        
instance Applicative (State xs) where
    pure x = State (x :-)
    fs <*> xs = State (\s -> case runState fs s of
        (f :- s') -> case runState xs s' of
            (x :- s'') -> f x :- s'')
            
instance Monad (State xs) where
    xs >>= f = State (\s -> case runState xs s of
        y :- ys -> runState (f y) ys)
```

# Polymorphism

But what's the point?
So far we've basically just encoded an unnecessarily complicated state
transformer.
Think back to the stacking of states.
Written in the [mtl](https://hackage.haskell.org/package/mtl) style, the main
advantage of stacking monads like that is you can write code like the following: 

```haskell
pop :: (MonadState [a] m, MonadError String m) => m a
pop = get >>= \case
    [] -> throwError "pop: empty list"
    x:xs -> do
        put xs 
        pure x
```

In other words, we don't care about the rest of `m`, we just care that it has,
somewhere, state for an `[a]`.

This logic should apply to our stack transformer, as well.
If it only cares about the top two variables, it shouldn't care what the rest of
the list is.
In types:

```haskell
infixr 0 :->
type (:->) xs ys = forall zs. Stack (xs ++ zs) -> Stack (ys ++ zs)
```

And straight away we can write some of the standard combinators:

```haskell
dup :: '[a] :-> '[a,a]
dup (x :- xs) = (x :- x :- xs)

swap :: '[x,y] :-> '[y,x]
swap (x :- y :- xs) = y :- x :- xs

drop :: '[x,y] :-> '[y]
drop (_ :- xs) = xs

infixl 9 !
(f ! g) x = g (f x)
```

You'll immediately run into trouble if you try to work with some of the more
involved combinators, though.
Quote should have the following type, for instance:

```haskell
quote :: (xs :-> ys) -> '[] :-> '[ xs :-> ys ]
```

But GHC complains again:

```
• Illegal polymorphic type: xs :-> ys
  GHC doesn't yet support impredicative polymorphism
• In the type signature:
    quote :: (xs :-> ys) -> '[] :-> '[xs :-> ys]
```

I won't go into the detail of this particular error: if you've been around the
block with Haskell you know that it means "wrap it in a newtype".
If we do *that*, though, we get yet more errors:

```haskell
newtype (:~>) xs ys = Q { d :: xs :-> ys }
```
```
• Couldn't match type ‘ys ++ zs0’ with ‘ys ++ zs’
  Expected type: Stack (xs ++ zs) -> Stack (ys ++ zs)
    Actual type: Stack (xs ++ zs0) -> Stack (ys ++ zs0)
  NB: ‘++’ is a type function, and may not be injective
```

This injectivity error comes up often.
It means that GHC needs to prove that the input to two functions is equal, but
it only knows that their outputs are.
This is a doubly serious problem for us, as we can't do type family injectivity
on two type variables (in current Haskell).
To solve the problem, we need to rely on a weird mishmash of type families and
functional dependencies:

```haskell
type family (++) xs ys where
    '[] ++ ys = ys
    (x : xs) ++ ys = x : (xs ++ ys)
    
class (xs ++ ys ~ zs) => Conc xs ys zs | xs zs -> ys where
    conc :: Stack xs -> Stack ys -> Stack zs
    
instance Conc '[] ys ys where
    conc _ ys = ys
    
instance Conc xs ys zs => Conc (x : xs) ys (x : zs) where
    conc (x :- xs) ys = x :- conc xs ys

infixr 0 :->
type (:->) xs ys = forall zs yszs. Conc ys zs yszs => Stack (xs ++ zs) -> Stack yszs
```

And it does indeed work:

```haskell
pure :: a -> '[] :-> '[a]
pure = (:-)

newtype (:~>) xs ys = Q { d :: xs :-> ys }

quote :: (xs :-> ys) -> '[] :-> '[ xs :~> ys ]
quote x = pure (Q x)

dot :: forall xs ys. ((xs :~> ys) : xs) :-> ys
dot (x :- xs) = d x xs

true :: (xs :~> ys) : (xs :~> ys) : xs :-> ys
true = swap ! drop ! dot

false :: (xs :~> ys) : (xs :~> ys) : xs :-> ys
false = drop ! dot

test :: '[] :-> '[ '[a] :~> '[a,a] ]
test = quote dup
```
