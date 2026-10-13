# Gluing EPPA

Lean formalization of the relational gluing-diagram construction.

**No manuscript sources are stored in this repository.**

The toolchain, pinned Mathlib revision, shared-cache CI and axiom-audit conventions are adapted from `janhubicka/lean-successors`, inspected at `dbcd157d5eee426c533da761ba979ccf78cb070e`.

## Checked snapshot

PR #1 was merged after the 14-declaration axiom audit in Actions run `38436358688`. PR #3 subsequently merged the concrete permutation-base module, whose 18-declaration audit passed in run `38440355549` at source commit `b790d8331ff464eeb76addd0705ab35dfa2922bc`.

- Source head: `aa1bdcb3efde6e89ed2fde23f53bde4d2db7ec63`.
- Actions checkout: `676ebf0b9300ab2a936acac6d0389f8298b4d1d9`.
- Identical source tree: `1e62523ad4235931a63132d79023218470c179af`.
- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: `5bd58ac291422a21f412ae354c91e7d172255a2c`.

The audit allows only `propext`, `Classical.choice`, and `Quot.sound`; it rejects `sorryAx` and custom assumed axioms.

## Modules

- `Basic`: point transports, reachability quotient, faithful frames and path uniqueness.
- `Relational`: arity-indexed relations (including repeated coordinates and arity zero), induced embeddings, quotient semantics, obstruction extraction and realization-to-free-realization.
- `Parity`: Boolean-cover odd-support connectivity between projected endpoints, proved by a cut potential over `ZMod 2`.
- `Replay`: simultaneous transport along a common supported base walk.
- `Cover`: changed-coordinate traversal witnesses, availability in both directions, induced free realization and finiteness.
- `Symmetry`: descent to quotient automorphisms and the incoming-edge extension equation.
- `AffineLift`: edge-coordinate permutations, fixed translations, lifted symmetries and rooted extensions.
- `PermutationDiagram`: the concrete permutation-base transport orientation, unique generator labels, faithful frame, local relation preservation, left multiplication and incoming root edge. **Kernel checked and merged.**

`cover_compatible` assumes a faithful empty-language frame and local relation preservation by each base edge. It proves global compatibility; it does not assume a relational realization or EPPA. `liftSymmetry` takes the induced edge permutation and incidence equivariance explicitly.

## Remaining work

This is **not yet an unconditional formalization of finite relational EPPA**.

1. Formalize distinguished inverse-compatible permutation extensions on a finite padded set.
2. Verify the exact unordered base-edge action on the manuscript's Boolean coordinates. A draft `OrientedCover` uses two parallel coordinates per undirected edge, so is a *different indexing* even though it applies the same generic theorem.
3. Instantiate the edge permutation and rooted extension interface for all labelled partial automorphisms.
4. Package the finite quotient and all extensions as the unconditional theorem. The manuscript's numerical padding bound is not yet formalized.

## Build and audit

```sh
lake update
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean > axioms.log
python3 scripts/check-axiom-log.py axioms.log
```

CI retains the build log, axiom output, resolved dependency manifest and checked commit as a proof-audit artifact. Dependency caches are keyed to the pinned setup; pull-request caches remain scoped by GitHub. No manuscript TeX is included in those artifacts.
