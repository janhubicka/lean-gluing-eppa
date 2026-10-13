# Gluing EPPA — Lean validation

A Lean formalization of the finite relational EPPA theorem using gluing diagrams.
**No manuscript TeX or source draft is stored here.** The authors circulate and
version the manuscript separately.

## Kernel-checked theorem and construction

Theorem **`GluingEPPA.finite_relational_eppa_private`**
in `GluingEPPA/PrivateFiniteEPPA.lean` is *unconditional*: for every finite
relational structure (including repeated coordinates, nullary symbols and
empty partial automorphisms) it constructs one finite induced witness in which
every partial automorphism extends to a relation-preserving automorphism.
It does not assume coherent extensions or the existence of an EPPA witness.

The checked construction now uses BOTH:

- **Exactly one Boolean coordinate per unordered base edge**, matching the
  manuscript's `M` (modules `UnorderedEdges`, `UnorderedCover`,
  `UnorderedAssembly`, `UnorderedFiniteEPPA`).
- **Private transposition/three-cycle marker permutations** on
  `A ⊕ (I × Bool)`, extending all inverse-indexed partial maps, with
  distinct nonidentity labels and an exactly checked padded carrier size
  `|A| + 2|I|` (modules `PrivateCycles`, `PrivateCycleInjection`,
  `PaddedPrivateFamily`, `PrivateFiniteEPPA`).

For each two-label inverse orbit the three-cycle uses three of the four
reserved marker points; the fourth point is fixed. Sofia's manuscript
describes omitting this unused point, giving `2s+3t` rather than
`2(s+2t)` marker points. The Lean cardinal bound needed by the theorem
is fully proved; **that optional pruning is not separately formalized**.

**Checked source:** PR
[#9](https://github.com/janhubicka/lean-gluing-eppa/pull/9) at
`548c5df7bbd2124f51d18590f8078d0efb8f3575`; merged as
`137ff8144f70b4af12423f65f8fbc984fb8752eb`.

**Independent checks:**
[PR build](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38485444160)
and [merged-main build](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38485659390)
both passed the full build and **63-declaration axiom audit**.
The audit allows only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx` or custom assumed axioms occur in the checked declarations.

## Proof modules

- `Basic`, `Relational`: transport paths, quotient realizations,
  compatibility, relation reflection and induced copies.
- `Parity`, `Replay`, `Cover`: cut-potential parity, common-base-path
  replay and the finite relational Boolean cover.
- `Symmetry`, `AffineLift`, `PermutationDiagram`: quotient descent,
  affine lifts and the concrete permutation-base diagram.
- `UnorderedEdges`, `UnorderedCover`, `UnorderedAssembly`,
  `UnorderedFiniteEPPA`: the exact undirected-edge construction.
- `PaddingCore`, `PartialFamily`, `RelPartialAut`: coherent total
  extensions of all relational partial automorphisms, including involutions.
- `Marker4`, `PaddedFamily`, `FiniteEPPA`: an earlier, fully checked,
  larger-marker alternative retained for comparison.
- `PrivateCycles`, `PrivateCycleInjection`, `PaddedPrivateFamily`,
  `PrivateFiniteEPPA`: the short private-cycle construction and final theorem.

## Reproducible CI and shared caches

Lean `leanprover/lean4:v4.35.0-rc3`; Mathlib pinned at
`5bd58ac291422a21f412ae354c91e7d172255a2c`.

```sh
lake update
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean > axioms.log
python3 scripts/check-axiom-log.py axioms.log
```

CI is adapted from `janhubicka/lean-successors`. GitHub Actions caches the
pinned toolchain across builds and restores one shared pinned Lake workspace.
Only a successful `main` build **after the theorem and axiom audits pass**
seeds this large cache. PRs reuse it but never upload per-PR copies.
Artifacts retain commit IDs, build/axiom logs, dependency inputs and checksums.
The untracked generated manifest is intentionally omitted from the cache key
because the pinned dependency revision is already in `lakefile.toml`.
