---
title: Phases in Software Architecture
---

Presented at [FUNARCH 2023](https://icfp23.sigplan.org/home/funarch-2023).

[Pdf available here.](pdfs/phases-in-software-architecture.pdf)

The large-scale structure of executing a computation can often be thought of as
being separated into distinct phases. But the most natural form in which to
specify that computation may well have a different and conflicting structure.
For example, the computation might consist of gathering data from some
locations, processing it, then distributing the results back to the same
locations; it may be executed in three phases—gather, process, distribute—but
mostly conveniently specified orthogonally—by location. We have recently shown
that this multi-phase structure can be expressed as a novel applicative functor
(also known as an idiom, or lax monoidal functor). Here we summarize the idea
from the perspective of software architecture. At the end, we speculate about
applications to choreography and multi-tier architecture.

Bibtex:

```
@inproceedings{10.1145/3609025.3609479,
author = {Gibbons, Jeremy and Kidney, Donnacha Ois\'{\i}n and Schrijvers, Tom and Wu, Nicolas},
title = {Phases in Software Architecture},
year = {2023},
isbn = {9798400702976},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
url = {https://doi.org/10.1145/3609025.3609479},
doi = {10.1145/3609025.3609479},
abstract = {The large-scale structure of executing a computation can often be thought of as being separated into distinct phases. But the most natural form in which to specify that computation may well have a different and conflicting structure. For example, the computation might consist of gathering data from some locations, processing it, then distributing the results back to the same locations; it may be executed in three phases—gather, process, distribute—but mostly conveniently specified orthogonally—by location. We have recently shown that this multi-phase structure can be expressed as a novel applicative functor (also known as an idiom, or lax monoidal functor). Here we summarize the idea from the perspective of software architecture. At the end, we speculate about applications to choreography and multi-tier architecture.},
booktitle = {Proceedings of the 1st ACM SIGPLAN International Workshop on Functional Software Architecture},
pages = {29–33},
numpages = {5},
keywords = {phase separation, traversal, applicative functor, fusion, choreography, multi-tier},
location = {Seattle, WA, USA},
series = {FUNARCH 2023}
}
```
