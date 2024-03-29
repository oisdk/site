---
title: Algebras for Weighted Search
---

Presented at [ICFP 2021](https://icfp21.sigplan.org).

[Pdf available here.](pdfs/algebras-for-weighted-search.pdf)

Weighted search is an essential component of many fundamental and useful
algorithms. Despite this, it is relatively under explored as a computational
effect, receiving not nearly as much attention as either depth- or breadth-first
search. This paper explores the algebraic underpinning of weighted search, and
demonstrates how to implement it as a monad transformer. The development first
explores breadth-first search, which can be expressed as a polynomial over
semirings. These polynomials are generalised to the free semimodule monad to
capture a wide range of applications, including probability monads, polynomial
monads, and monads for weighted search. Finally, a monad transformer based on
the free semimodule monad is introduced. Applying optimisations to this type
yields an implementation of pairing heaps, which is then used to implement
Dijkstra's algorithm and efficient probabilistic sampling. The construction is
formalised in Cubical Agda and implemented in Haskell.

Bibtex:

```tex
@article{10.1145/3473577, 
author = {Kidney, Donnacha Ois\'{\i}n and Wu, Nicolas}, 
title = {Algebras for Weighted Search}, 
year = {2021},
issue_date = {August 2021}, 
publisher = {Association for Computing Machinery}, 
address = {New York, NY, USA}, 
volume = {5},
number = {ICFP}, 
url = {https://doi.org/10.1145/3473577},
doi = {10.1145/3473577}, 
abstract = {Weighted search is an essential component of many fundamental and useful algorithms. Despite this, it is relatively under explored as a computational effect, receiving not nearly as much attention as either depth- or breadth-first search. This paper explores the algebraic underpinning of weighted search, and demonstrates how to implement it as a monad transformer. The development first explores breadth-first search, which can be expressed as a polynomial over semirings. These polynomials are generalised to the free semimodule monad to capture a wide range of applications, including probability monads, polynomial monads, and monads for weighted search. Finally, a monad transformer based on the free semimodule monad is introduced. Applying optimisations to this type yields an implementation of pairing heaps, which is then used to implement Dijkstra's algorithm and efficient probabilistic sampling. The construction is formalised in Cubical Agda and implemented in Haskell.}, 
journal = {Proc. ACM Program. Lang.},
month = {aug}, 
articleno = {72},
numpages = {30},
keywords = {Haskell, monad, Agda, graph search} 
}
```
