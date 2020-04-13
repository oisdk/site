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
  = Trie
  { _done :: Bool
  , _step :: Map a (Trie a)
  }

makeLenses ''Trie
```

Yes we're jumping straight into the lenses already, but don't worry: we're just
defining the basic fields as lenses.

```haskell
empty :: Trie a
empty = Trie False Map.empty

isEmpty :: Trie a -> Bool
isEmpty (Trie x xs) = not x && Map.null xs

word :: Ord a => [a] -> Lens' (Trie a) Bool
word = foldr (\x xs -> step . at x . anon empty isEmpty . xs) done
```
