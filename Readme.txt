Associated material for the paper "Proving Correctness of Compilers
using Structured Graphs".

 * Coq proofs:
   - "Tree.v", "Graph.v": Definition of tree and graph types,
     respectively.
   - "GraphUnravel.v": Proof of Theorem 2.
   - "Compiler.v": Implementation of the tree-based and the graph-based
     compiler; proof of Lemma 1 from the paper.
   - "CalculationTactics.v": Tactics for program calculation proofs.
   - "Container.v": Formalisation of containers (used as a
     representation of strictly positive functors).
 * Literate Haskell source file for the paper: "paper.lhs".
 * The file "appendix.pdf" contains an appendix to the paper detailing
   the monadic approach.
