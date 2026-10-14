# Gluing EPPA — Lean validation

A Lean formalization of finite relational EPPA using gluing diagrams, followed
by validation of a proposed sparsening construction.
**No manuscript TeX or source draft is stored here.**

## Unconditional finite relational EPPA

`GluingEPPA.finite_relational_eppa_private` constructs one finite induced witness
extending all partial automorphisms of any finite relational structure. It
assumes neither a witness nor inverse-compatible total extensions. Nullary
relations, repeated tuple entries and empty partial automorphisms are included.
The construction uses one Boolean coordinate per unordered base edge and
private transposition/three-cycle markers on `A ⊕ (I × Bool)`. Distinctness,
nonidentity, inverse compatibility and the bound `|A| + 2|I|` are checked.
The optional pruning of unused markers to the smaller `2s+3t` count is not
separately formalized. `PartialFamily.coherentBase` means inverse-compatible
choices, NOT the composition requirement of coherent EPPA.

The ordinary-EPPA checkpoint is PR #9 at
`548c5df7bbd2124f51d18590f8078d0efb8f3575`, merged as
`137ff8144f70b4af12423f65f8fbc984fb8752eb`; both builds passed 63 audited targets.

## Sparsening: canonical atlas, local geometry and actions checked

**154 unique declarations** now pass the axiom audit, preserving all previous
132 targets. Only `propext`, `Classical.choice` and `Quot.sound` are permitted;
no `sorryAx` or custom assumed axiom occurs in their transitive dependencies.
**The full sparsening theorem remains pending.**

- PR #12: supported-walk converse, variable-size valid chart quotient and full
  unary fibres. Source `97f834c6639e0b2948d6c641323318bfb6e3e261`; run
  `38503255935`, 106 targets; merged `24f429e4adaa512efb40e384e7de8977a15ae8fe`.
- PR #13: actual chart-or-closed-separator certificate. Source
  `9216dcc8a72e7d69067395f90de7c988b740aabb`; PR run `38503944598` and main run
  `38504321125`, 119 targets.
- PR #14: generic affine quotient action, full unary fibres and actual endpoint
  equations. Source `2947c28fdd2996e3348375c64d3da52b2db3196d`; PR run
  `38565510278` and main run `38567430312`, 132 targets; merged
  `b4c2a22c28de7a4635beed161a6e930a2991232e`.
- PR [#15](https://github.com/janhubicka/lean-gluing-eppa/pull/15): canonical
  orbit atlas, its full relational/unary automorphisms, endpoint composition
  and automorphic chart movement. Source
  `835e18e29d0664ff78edffc4ce9e3f524e2558b7`; merged
  `82d5b2299aeab292aa5d2fe9e73a450bc2d9f44b`.
  [PR run](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38573078116)
  and [main run](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38574191452)
  both passed the full build, **154-target audit** and all three regression suites.
  Downloaded artifact hashes, every internal checksum and all unique axiom
  outputs were checked; local and CI orbit-regression results agree exactly.

### Local geometry

`CompleteRecords` constructs supported walks from equality of pointed boundary
charge and exterior coordinates, by rooted excursions and an endpoint spoke.
Disconnected parity support, loops, parallel edges and zero-length walks are
handled. `ChartAtlas` uses only valid occurrences `(s,chi,x)` with `x ∈ s`;
canonical charts are induced and compatible records give an actual common
lifted chart. `UnaryAtlas` proves representative independence of entire unary
fibres and `p[F_new(q)] = F_old(p(q))`, including branching and cyclic outputs.
`AtlasRecords` derives local agreement from contributing charts.
`AtlasSeparator` gives an actual common chart or a proper closed cut, with
ambient-closed sides and a closed projected separator root.

### Affine actions and the canonical orbit

`AtlasAction`, `AtlasUnaryAction` and `AtlasEndpoint` prove the generic action

    L(h,delta)[s,chi,x] = [h(s),h_*chi+delta,h(x)]
    L(g,epsilon) L(h,delta) = L(gh,epsilon+g_*delta),

including quotient descent, inverse, full unary-fibre equality, uniform root
spokes, endpoint extension/composition and exact chart images.

`CompleteChartGraph` now supplies the actual complete loopless unordered graph
and induced edge actions with identity and composition. `OrbitAtlas` takes
charts to be ACTUAL closed subsets contained in some `h[A]`, not embedding
presentations; set-image actions compose and preserve closure. Empty charts
and finite chart carriers are derived without assuming the old root orbit
covers the ambient carrier.

`OrbitAction.canonical` instantiates all membership/incidence hypotheses.
`OrbitAction.lift` is an actual combined relational/unary automorphism for each
old automorphism and translation. `OrbitEndpoint.endpoint_extends`,
`endpoint_comp` and `endpoint_identity` concern canonical quotient maps with
actual domain/range charts, not an abstract supplied action.
`liftedChart_in_full` uses a single uniform spoke for a whole smaller chart.
`fullChart_to_root` sends every lifted full chart exactly onto the root;
`chart_to_root` moves every smaller lifted chart inside it. No upstairs
transitivity or automorphism existence is an input assumption.

This is the automorphism part of faithfulness, NOT yet the semantic theorem
that EVERY irreducible substructure lies in a chart.

### Independent finite implementations

CI runs three supplementary Python suites. They are not substitutes for Lean
proofs or independent mathematical referee reports.

- `check_saturated_cover.py`: local quotient/parity/separator checks.
- `check_atlas_action.py`: union-find quotient checks of affine actions, full
  unary fibres and mutations of the coordinate/inverse-translation rules.
- `check_orbit_atlas.py`: enumerates old automorphisms and actual closed-subset
  orbits, then computes the supported quotient by union-find, not records.
  Five cases include empty roots, proper root orbits, branching unary fibres
  and overlapping root images with a closed common sink. It checks 149,504
  affine occurrence evaluations, 800 chart-movement point equations, 149
  composable endpoint pairs and 13,728 quotient composition equations. A
  nonempty proper-domain extension genuinely moves the root chart. Freezing
  chart indices while moving points is detected as an incorrect rule.

### Remaining obligations

Formalize the irreducibility/free-amalgam semantic bridge, identify the
auxiliary contributed relation J with chart adjacency, derive irreducible
containment and hence faithfulness and the projection homomorphism-embedding.
The converse identifying all automorphic A-copies with controlled full charts
also still requires this bridge. Package the simultaneous partial-automorphism
extension choices and their coherence when supplied downstairs. Then assemble
strict tree amalgamation, the local size induction, iteration and final reduct.
The checked endpoint cocycle by itself is not the full coherent sparsening
theorem. Independent mathematical referee review remains outstanding.

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

CI is adapted from `janhubicka/lean-successors`. Actions caches the pinned
toolchain and restores one shared pinned Lake workspace. Only a successful
main build after all proof/audit/regression gates pass seeds the large cache;
PRs reuse it without per-PR uploads. Artifacts retain commits, logs, dependency
inputs and SHA256SUMS. The generated manifest is omitted from the cache key
because the revision is pinned in `lakefile.toml`. PR #15 changes no cache keys
or seeding policy; it only adds the orbit-regression command to the test gate.
