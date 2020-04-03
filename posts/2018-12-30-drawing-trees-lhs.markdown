---
title: Drawing Trees
tags: Haskell
---

For a bunch of algorithms it's handy to get a quick-and-dirty visualization of a
tree.
[Data.Tree](http://hackage.haskell.org/package/containers-0.6.0.1/docs/Data-Tree.html#v:drawTree)
has a tree-drawing function, but its output is too noisy for my taste, and so
doesn't really illustrate the underlying structure in a way I find helpful. This
version uses the unicode box-drawing characters to give an output that's midway
between what is provided in
[Data.Tree](http://hackage.haskell.org/package/containers-0.6.0.1/docs/Data-Tree.html#v:drawTree)
and a full-blown SVG diagram. This makes it perfect for debugging tree-based
algorithms while you're writing them.

For the [example tree in Wikipedia's article on breadth-first
search](https://en.wikipedia.org/wiki/Breadth-first_search), it gives the
following output:

```
     ┌─9
   ┌5┤
 ┌2┤ └10
 │ └6
1┼3
 │   ┌11
 │ ┌7┤
 └4┤ └12
   └8
```

```haskell
module TreeDrawing where

import Data.Tree (Tree(..))
import Data.List (intercalate)

drawTree :: Tree String -> String
drawTree tr = (unlines . filter content . flatten) (foldr go undefined maxLengths withLength)
  where
    withLength = fmap (\x -> (length x, x)) tr
    maxLengths = lwe withLength (repeat 0)
    lwe (Node x xs) (q:qs) = max (fst x) q : foldr lwe qs xs
    
    content = any (`notElem` " │")
    flatten (ls,x,rs) = ls ++ [x] ++ rs
    mapZipper lf f rf (ls,x,rs) = (map lf ls, f x, map rf rs)
    toZipper xs = case splitAt (length xs `div` 2) xs of (ls,x:rs) -> (ls,x,rs)
    
    go m ls (Node (l,x) []) = ([],replicate (m-l) '─' ++ x,[])
    go m ls (Node (l,x) [y]) = mapZipper pad link pad (ls y)
      where
        padding = m + 1
        pad = (++) (replicate padding ' ')
        link z = replicate (m-l) '─' ++ x ++ "─" ++ z
    go m ls (Node (l,x') xs) = mapZipper pad link pad (toZipper (intercalate ["│"] ([ysh] ++ ysm ++ [ysl])))
      where 
        x = replicate (m-l) '─' ++ x'
        ys = map ls xs
        
        ysh = flatten (mapZipper (' ':) ('┌' :) ('│':) (head ys))
        ysl = flatten (mapZipper ('│':) ('└' :) (' ':) (last ys))
        ysm = map (flatten . mapZipper ('│':) ('├':) ('│':)) (init (tail ys))
        
        pad = (++) (replicate m ' ')
        
        link ('│':zs) = x ++ "┤" ++ zs
        link ('├':zs) = x ++ "┼" ++ zs
        link ('┌':zs) = x ++ "┬" ++ zs
        link ('└':zs) = x ++ "┴" ++ zs
```
