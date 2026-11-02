# Lean Work

This repository contains my ongoing **Lean 4 learning and research work** in formal methods, software verification, and automated reasoning. 

## PolyContracts

`PolyContracts` is the main formalisation project in this repository. It explores the mechanisation of a component-based formal model for distributed and cyber-physical systems.

The current Lean development covers:

- components, methods, jobs, and behaviours;
- typed input, output, and inout parameters;
- return values and exceptions;
- public/private methods and method kinds;
- component references and run-time instances;
- reference resolution and target uniqueness;
- contextual environments;
- requiring relations between components;
- attribute and local-variable update sets;
- structural well-formedness properties.

Definitions and proofs are kept in separate files. The accompanying property files establish machine-checked results such as partitioning and disjointness, membership characterisations, uniqueness properties, well-formedness conditions, and consistency between the different layers of the model.

## Inductive Verification

The repository also contains smaller Lean projects used to explore **inductive verification and solver construction**.

`KInduction` experiments with implementing the reasoning principles behind a simple k-induction solver directly in Lean. The objective is to understand how base checks, inductive steps, executable checking, and soundness proofs can be connected within the theorem prover.

`KInductiveCounter` applies this approach to a small counter model, combining executable checks with machine-checked proofs.

The `counter` project contains a simpler example of proving a safety property using direct inductive reasoning and auxiliary invariants.

## Purpose

This repository is primarily a **learning and research workspace**. It is used to experiment with:

- Lean 4 theorem proving;
- formalisation of software-system models;
- inductive invariants and k-induction;
- executable verification procedures;
- machine-checked reasoning about components and interfaces;
- connections between automated reasoning and interactive theorem proving.

The emphasis is on progressively translating verification concepts and research models into explicit, understandable, and machine-checked Lean developments.

## Building

Each directory is a Lean/Lake project. With Lean installed through `elan`, a project can typically be checked with:

```bash
lake exe cache get
lake build
```