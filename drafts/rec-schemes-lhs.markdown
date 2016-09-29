---
title: Recursion Schemes Examples
tags: Haskell
bibliography: Recursion Schemes.bib
---
```{.haskell .literate .hidden_source}
module RecSchemes where
```
Recursion schemes are one of the areas in Haskell that is usually regarded as "advanced". Blog posts on the topic are in danger of becoming the new [monad tutorial](https://wiki.haskell.org/Monad_tutorials_timeline). On top of that, they have not demonstrated the same overwhelming usefulness in general programming as something like monads, so it's hard to justify learning the abstraction. (or, at the very least, [the more obscure corners](https://wiki.haskell.org/Zygohistomorphic_prepromorphisms) of the abstraction)

That said, they're very interesting!

The original paper [@meijer_functional_1991] is excellent, but a little dense. 
