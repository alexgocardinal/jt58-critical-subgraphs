# Jensen–Toft Problem 5.8

A Lean formalization of a nine-vertex counterexample to the literal
noninduced-critical-subgraph question in Jensen and Toft,
Graph Coloring Problems, Section 5.8.

Author: Alex Chan
Harvard University and National Bureau of Economic Research
achan@hbs.edu

## Main result

The theorem JT58.jt58_counterexample proves that the explicit host graph:

- is 5-critical with respect to all proper subgraphs;
- is not complete;
- has no noninduced 4-critical subgraph.

Subgraphs may omit both vertices and edges.

The formalization uses explicit coloring certificates and a direct case
proof covering every subset of the 19 host edges. Python generates proof
files; Lean checks the resulting proofs independently.

The main theorem depends only on propext, Classical.choice, and Quot.sound.
It uses neither sorryAx nor a native-checker axiom.
Mathlib is not required.

## Verification

Install Lean using elan. In this directory, run: lake build

The pinned version is recorded in lean-toolchain.

The main statement is in JT58/MainTheorem.lean.
The graph is in JT58/Graph.lean.
The direct coverage proof is in JT58/KernelCoverage.lean.

## Scope and provenance

The host is the classical graph commonly denoted O_5.
The formal theorem establishes its counterexample property.
Claims about publication priority require a separate literature review.

The checked-in Lean files suffice to build the proof; running the Python
generators is not required.
