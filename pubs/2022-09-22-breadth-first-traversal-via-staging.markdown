---
title: Breadth-First Traversal via Staging
---

Presented at MPC 2022.

[Pdf available here.](pdfs/breadth-first-traversals-via-staging.pdf)

An effectful traversal of a data structure iterates over every element, in some
predetermined order, collecting computational effects in the process.
Depth-first effectful traversal of a tree is straightforward to define
compositionally, since it precisely follows the shape of the data. What about
breadth-first effectful traversal? An indirect route is to factorize the data
structure into shape and contents, traverse the contents, then rebuild the data
structure with new contents. We show that this can instead be done directly
using staging, expressed using a construction related to free applicative
functors. The staged traversals lend themselves well to fusion; we prove a novel
fusion rule for effectful traversals, and use it in another solution to Bird's
`repmin' problem.

Bibtex:

```
@InProceedings{10.1007/978-3-031-16912-0_1,
author="Gibbons, Jeremy
and Kidney, Donnacha Ois{\'i}n
and Schrijvers, Tom
and Wu, Nicolas",
editor="Komendantskaya, Ekaterina",
title="Breadth-First Traversal via Staging",
booktitle="Mathematics of Program Construction",
year="2022",
publisher="Springer International Publishing",
address="Cham",
pages="1--33",
abstract="An effectful traversal of a data structure iterates over every element, in some predetermined order, collecting computational effects in the process. Depth-first effectful traversal of a tree is straightforward to define compositionally, since it precisely follows the shape of the data. What about breadth-first effectful traversal? An indirect route is to factorize the data structure into shape and contents, traverse the contents, then rebuild the data structure with new contents. We show that this can instead be done directly using staging, expressed using a construction related to free applicative functors. The staged traversals lend themselves well to fusion; we prove a novel fusion rule for effectful traversals, and use it in another solution to Bird's `repmin' problem.",
isbn="978-3-031-16912-0"
}
```
