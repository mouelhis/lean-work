# PolyContracts

Lean 4 mechanisation of the Poly-Contracts formalism for distributed
object-oriented component-based cyber-physical systems.

The project currently formalises:

- component methods and their visibility;
- services, commands, data sources, and data wells;
- public/private and method-kind partitions;
- local and remote component references;
- structural well-formedness properties;
- machine-checked proofs of partition, disjointness, coverage, and related properties.

## Structure

- `PolyContracts/Basic.lean` — primitive types and classifications.
- `PolyContracts/Component.lean` — component and method definitions.
- `PolyContracts/ComponentProperties.lean` — machine-checked structural properties.

## Build

The project uses Lean 4 and Mathlib.

```bash
lake build