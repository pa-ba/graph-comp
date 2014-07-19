Proving Correctness of Compilers Using Structured Graphs
========================================================

Coq proofs for the paper
["Proving Correctness of Compilers Using Structured Graphs"](http://dx.doi.org/10.1007/978-3-319-07151-0_14):

- [Tree.v](Tree.v), [Graph.v](Graph.v): Definition of tree and graph
  types, respectively.
- [GraphUnravel.v](GraphUnravel.v): Proof of Theorem 2.
- [Compiler.v](Compiler.v): Implementation of the tree-based and the
  graph-based compiler; proof of Lemma 1 from the paper.
- [CalculationTactics.v](CalculationTactics.v): Tactics for program
  calculation proofs.
- [Container.v](Container.v): Formalisation of containers (used as a
  representation of strictly positive functors).
