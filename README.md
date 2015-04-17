# Proving Correctness of Compilers Using Structured Graphs [![Build Status](https://travis-ci.org/pa-ba/graph-comp.svg?branch=master)](https://travis-ci.org/pa-ba/graph-comp)


Coq proofs for the paper
["Proving Correctness of Compilers Using Structured Graphs"](http://dx.doi.org/10.1007/978-3-319-07151-0_14).

## File Structure

- [Tree.v](Tree.v), [Graph.v](Graph.v): Definition of tree and graph
  types, respectively.
- [GraphUnravel.v](GraphUnravel.v): Proof of Theorem 2.
- [Compiler.v](Compiler.v): Implementation of the tree-based and the
  graph-based compiler; proof of Lemma 1 from the paper.
- [CalculationTactics.v](CalculationTactics.v): Tactics for program
  calculation proofs.
- [Container.v](Container.v): Formalisation of containers (used as a
  representation of strictly positive functors).

## Technical Details

### Dependencies

- To check the proofs: Coq 8.4pl5
- To step through the proofs: GNU Emacs 24.3.1, Proof General 4.2

### Proof Checking

To check and compile the complete Coq development, you can use the
`Makefile`:

```shell
> make
```
