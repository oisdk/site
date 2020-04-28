---
title: Using Lenses to Implement Data Structures
tags: Haskell
---

# A Trie

Tries are data structures for sequences, which function much like a search tree.
They themselves are trees, although at each leaf instead of containing a
key-value pair, the key is taken as the concatenation of all its *ancestor's*
keys.
The following diagram might explain the idea more succinctly:

![](../images/Trie.svg)

Tries have numerous uses, but they can be a little tricky to implement.
I'm going to show today how lenses can ease the burden a little bit by
clarifying our thoughts for us.

Bear in mind this is *not* a lens tutorial, so I'm expecting at least a little
familiarity with the main Haskell lens library going in.

# The Data Type

We will first need to define a type for tries:

```haskell
data Trie a
  = (:<)
  { _done :: Bool
  , _step :: Map a (Trie a)
  }

makeLenses ''Trie
```

Yes we're jumping straight into the lenses already, but don't worry: we're just
defining the basic fields as lenses.

# Lookup

Let's look at defining an operation without the lenses, in a relatively standard
way.
Lookup is certainly the easiest:

```haskell
member :: Ord a => [a] -> Trie a -> Bool
member []     (y :< _ ) = y
member (x:xs) (_ :< ys) = maybe False (member xs) (Map.lookup x ys)
```

We're not using any fancy tricks here for explanatory purposes.
In our path to use lenses, however, it is instructive to try and fancy this
function up a little.
Best stick in a fold, then:

```haskell
member :: Ord a => [a] -> Trie a -> Bool
member = foldr f b
  where
    b (y :< _) = y
    f x xs (_ :< ys) = maybe False xs (Map.lookup x ys)
```

Also it might be a little cleaner to just use field accessors instead of
pattern-matching.

```haskell
member :: Ord a => [a] -> Trie a -> Bool
member = foldr f _done
  where
    f x xs = maybe False xs . Map.lookup x . _step
```

Pretty clean! 
I don't think we can improve this function very much.


# Insert

After lookup, the next most difficult function is probably insert.
Again, we will start with the very plain pattern-matching definition.


```haskell
emptyTrie :: Trie a
emptyTrie = False :< Map.empty

insert :: Ord a => [a] -> Trie a -> Trie a
insert []     (_ :< ys) = True :< ys
insert (x:xs) (y :< ys) = y    :< Map.alter (Just . insert xs . fromMaybe emptyTrie) x ys
```

Again, first way we make this a little more slick is that we use a fold:

```haskell
insert :: Ord a => [a] -> Trie a -> Trie a
insert = foldr f b
  where
    b      (y :< ys) = True :< ys
    f x xs (y :< ys) = y    :< Map.alter (Just . xs . fromMaybe emptyTrie) x ys
```

The next move is not exactly the same as we had previously: we can't just use
the field accessors.
Instead, we want to map a function *over* the field, perhaps the classic use of
a lens.

```haskell
insert :: Ord a => [a] -> Trie a -> Trie a
insert = foldr f (done .~ True)
  where
    f x xs = step %~ Map.alter (Just . xs . fromMaybe emptyTrie) x
```

Pretty clean! Let's move to the next operation.

# Delete

This one is a bit more tricky.
Let's start again with the pattern-matching definition:

```haskell
delete :: Ord a => [a] -> Trie a -> Trie a
delete []     (_ :< ys) = False :< ys
delete (x:xs) (y :< ys) = y     :< Map.alter (fmap (delete xs)) x ys
```

This contains a subtle bug.
Consider the trie representing the string "carrot".
It will be basically a singly-linked-list of the letters, ending in a trie with
a `True` tag.
If we delete that string with the above function, we will be left with the
singly-linked list, with a `False` tag at the end.

So we have to engage in some ugly testing to check if the now-deleted subtrie is
empty, in which case it should be removed from the map.

```haskell
isEmpty :: Trie a -> Bool
isEmpty (x :< xs) = not x && Map.null xs

ensure :: (a -> Bool) -> a -> Maybe a
ensure p x
  | p x       = Just x
  | otherwise = Nothing
    
delete :: Ord a => [a] -> Trie a -> Trie a
delete []     (_ :< ys) = False :< ys
delete (x:xs) (y :< ys) = y     :< Map.alter ((ensure (not . isEmpty) . delete xs) =<<) x ys
```

# Using Lenses

There are numerous problems with the above functions:

* They are complex, and error-prone.
* They are difficult to understand.
* They have huge amounts of repetition.

We're going to fix all of these problems by using lenses to define these
functions from the get-go.
In fact, we're going to be able to define them all at once!

Let's start with what we want to figure out conceptually: a lens from a given
key into its presence in the trie.
In types:

```haskell
string :: Ord a => [a] -> Lens' (Trie a) Bool
```

The key which will simplify all of the implementation is that we're going to
keep it extremely high-level, using lenses as much as possible.
We will start with a fold:


```haskell
string :: forall a. Ord a => [a] -> Lens' (Trie a) Bool
string = foldr f b
  where
    b :: Lens' (Trie a) Bool
    b = _

    f :: a -> Lens' (Trie a) Bool -> Lens' (Trie a) Bool
    f x xs = _
```

We need to next fill in the holes.
The first (`b`) is simple: the lens into the corresponding `Bool` for an empty
string is the `Bool` in the root trie.

```haskell
string :: forall a. Ord a => [a] -> Lens' (Trie a) Bool
string = foldr f b
  where
    b :: Lens' (Trie a) Bool
    b = done

    f :: a -> Lens' (Trie a) Bool -> Lens' (Trie a) Bool
    f x xs = _
```

Next we need to join up some lenses to step down a level in the tree.
Again, this is relatively simple:

```haskell
string :: forall a. Ord a => [a] -> Lens' (Trie a) Bool
string = foldr f b
  where
    b :: Lens' (Trie a) Bool
    b = done

    f :: a -> Lens' (Trie a) Bool -> Lens' (Trie a) Bool
    f x xs = step . at x . xs
```

Unfortunately this won't actually work.
The `at x` expression produces a lens into a `Maybe (Trie a)`, rather than a
`Trie a`.

This error actually helps us a little: it can help us avoid the error we had
with deletion.
Theory-wise, the map entry that corresponds to `Nothing` should be treated the
same way we treat an empty trie.
Luckily there's a lens combinator precisely for this: `anon`.
Using it, we get the following extremely simple function:

```haskell
string :: Ord a => [a] -> Lens' (Trie a) Bool
string = foldr (\x xs -> step . at x . anon emptyTrie isEmpty . xs) done
```

From this we can pretty simply implement all the previous functions we had:

```haskell
member :: Ord a => [a] -> Trie a -> Bool
member xs = view (string xs)

insert :: Ord a => [a] -> Trie a -> Trie a
insert xs = string xs .~ True

delete :: Ord a => [a] -> Trie a -> Trie a
delete xs = string xs .~ False
```

# Uses

The first use for this structure is pretty obvious: string search.
Storing strings in a map can be extremely inefficient, resulting in a huge
number of extra comparisons on common prefixes.

# Autocompletion

Another interesting use is as a way to drive auto completion.
Now, the resulting auto complete won't actually be very good, since it will not
do any fuzzy matching, but it will give us all the suffixes to a given word.
Here's the appropriate lens:

```haskell
suffixes :: Ord a => [a] -> Lens' (Trie a) (Trie a)
suffixes = foldr (\x xs -> step . at x . anon emptyTrie isEmpty . xs) id
```

Now we want to get the strings out of this subtrie.
Here's how we can do that:

```haskell
foldrTrie :: ([a] -> b -> b) -> b -> Trie a -> b
foldrTrie f b ~(x :< xs) = (if x then f [] else id) 
                         $ Map.foldrWithKey (\k -> flip (foldrTrie (f . (k:)))) b xs

trieToList :: Trie a -> [[a]]
trieToList = foldrTrie (:) []
```

Now we can build a dictionary from something like [the full text of the
Adventures of Sherlock Holmes](http://www.gutenberg.org/ebooks/1661), and from
there perform the following:

```haskell
complete :: String -> [String]
complete xs = trieToList (dict ^. suffixes xs)

>>> complete "ana"
["lysis","lytical","tomy"]
```

# The Trie Monad
