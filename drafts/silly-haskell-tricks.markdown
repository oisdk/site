---
title: Silly Haskell Tricks You Probably Don't Know
tags: Haskell
---

I've been using Haskell for a while now, and I realise I've picked up quite a
few tips and tricks on the language and on GHC that even some advanced users
might not have come across.
So I'm going to collect some of them in this post!

None of these are really earth-shattering, it's meant to be more fun and weird
corners of GHC and stuff.

# Sharing Field Names

Until GHC 8.0.1 Haskell did not allow two declarations of the same field in the
same file.
After
[`-XDuplicateRecordFields`](https://downloads.haskell.org/ghc/latest/docs/html/users_guide/glasgow_exts.html#duplicate-record-fields),
however, we can now use duplicates to our heart's content.

Except... that's not really true.
There was *one* place where you could use the same field more than once: in the
same type.
What?

Consider the following binary tree type:

```haskell
data Tree a
  = Leaf { size :: Int, value :: a }
  | Node { size :: Int, lchild :: Tree a, rchild :: Tree a }
```

It might even be a surprise for some that we can use record fields in a sum type
(you shouldn't use them, by the way), but if some field name is shared across
two constructors we the field accessor you might expect!

# The `until` function

# Changing the default types
