# Gluing EPPA

Lean formalization of the relational gluing-diagram construction.

**No manuscript sources are stored in this repository.**

The Lean toolchain, pinned Mathlib revision, shared-cache CI, and axiom-audit conventions are adapted from `janhubicka/lean-successors`, inspected at `dbcd157d5eee426c533da761ba979ccf78cb070e`.

## Scope

The initial modules implement transport paths, the free relational quotient, the obstruction criterion, realization-to-free-realization, and simultaneous replay along a common supported base walk. The finite permutation padding, Boolean-cover parity lemma, and full finite EPPA assembly are not yet claimed as formalized.

Build with `lake update`, `lake exe cache get`, and `lake build`. Run the declaration audit with `lake env lean scripts/CheckAxioms.lean`.
