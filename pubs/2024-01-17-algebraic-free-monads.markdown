---
title: Algebraic Effects Meet Hoare Logic in Cubical Agda
---

Presented at [POPL 2024](https://popl24.sigplan.org).

[Pdf available here.](pdfs/algebraic-free-monads.pdf)


This paper presents a novel formalisation of algebraic effects with equations in
Cubical Agda. Unlike previous work in the literature that employed setoids to
deal with equations, the library presented here uses quotient types to
faithfully encode the type of terms quotiented by laws. Apart from tools for
equational reasoning, the library also provides an effect-generic Hoare logic
for algebraic effects, which enables reasoning about effectful programs in terms
of their pre- and post- conditions. A particularly novel aspect is that
equational reasoning and Hoare-style reasoning are related by an elimination
principle of Hoare logic.


Bibtex:

```tex
@inproceedings{kidney_algebraic_2024,
  title = {Algebraic {{Effects Meet Hoare Logic}} in {{Cubical Agda}}},
  booktitle = {Proceedings of the 51st {{Annual ACM SIGPLAN-SIGACT Symposium}} on {{Principles}} of {{Programming Languages}} - {{POPL}} 2024},
  author = {Kidney, Donnacha Ois{\'i}n and Yang, Zhixuan and Wu, Nicolas},
  year = {2024},
  month = jan,
  publisher = {{ACM Press}},
  address = {{Institution of Engineering and Technology (IET), Savoy Place, London}},
  abstract = {This paper presents a novel formalisation of algebraic effects with equations in Cubical Agda. Unlike previous work in the literature that employed setoids to deal with equations, the library presented here uses quotient types to faithfully encode the type of terms quotiented by laws. Apart from tools for equational reasoning, the library also provides an effect-generic Hoare logic for algebraic effects, which enables reasoning about effectful programs in terms of their pre- and post- conditions. A particularly novel aspect is that equational reasoning and Hoare-style reasoning are related by an elimination principle of Hoare logic.},
  langid = {english}
}
```
