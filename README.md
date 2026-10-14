# Gluing EPPA — Lean validation

A Lean formalization of finite relational EPPA using gluing diagrams, with a
second development of the proposed sparsening construction.
**No manuscript TeX or source draft is stored here.**

## Unconditional finite relational EPPA

`GluingEPPA.finite_relational_eppa_private` in `PrivateFiniteEPPA.lean` constructs
one finite induced witness extending all partial automorphisms of any finite
relational structure. It assumes neither an EPPA witness nor inverse-compatible
total extensions. Nullary relations, repeated tuple coordinates and empty
partial automorphisms are included.

The construction uses one Boolean coordinate per unordered base edge and
private transposition/three-cycle markers on `A ⊕ (I × Bool)`. Distinctness,
nonidentity, inverse compatibility and the size `|A| + 2|I|` are checked. The
unused fourth marker in each two-label inverse orbit is left fixed; the optional
pruning to the smaller `2s+3t` marker count is not separately formalized.

The ordinary-EPPA checkpoint is PR #9, source
`548c5df7bbd2124f51d18590f8078d0efb8f3575`, merged as
`137ff8144f70b4af12423f65f8fbc984fb8752eb`. Its PR and main builds passed the
then-current 63-declaration audit. The name `PartialFamily.coherentBase` means
inverse-compatible choices, **not** the composition requirement of coherent EPPA.

## Sparsening: concrete local geometry checked, full theorem pending

The library now passes a **119-declaration axiom audit**. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted; no `sorryAx` or custom
assumed axiom occurs in the audited declarations' transitive dependencies.

- PR #12, source `97f834c6639e0b2948d6c641323318bfb6e3e261`, added the actual
  supported-walk converse, valid variable-size chart quotient and full unary
  fibres. Run `38503255935` passed all gates with 106 audited declarations;
  merged as `24f429e4adaa512efb40e384e7de8977a15ae8fe`.
- PR #13, source `9216dcc8a72e7d69067395f90de7c988b740aabb`, derived the concrete
  chart-or-closed-separator certificate from the quotient. Run `38503944598`
  passed all gates with 119 audited declarations. Merged as
  `9d7e7cbfe19425ae9d5aebbfd675712770862bb3`; the independent merged-main run
  `38504321125` also passed the build, axiom audit and finite regressions.

### What the new modules prove

`Sparsening/CompleteRecords` constructs supported walks by concatenating rooted
excursions and an endpoint spoke. Equality of pointed boundary charge and of
exterior coordinates is equivalent to path equivalence on valid occurrences.
The proof handles disconnected parity support, loops, parallel edges, singleton
supports and zero-length walks. The complete graph and endpoint membership are
explicit hypotheses, not implicit connectivity assumptions.

`Sparsening/ChartAtlas` forms the quotient only from triples `(s,chi,x)` with
`x ∈ s`. Its fibrewise presentation over the unchanged ambient point contains
no artificial outside-chart vertices. Canonical charts are induced embeddings;
complete records and star correction give an actual common lifted chart.

`Sparsening/UnaryAtlas` proves representative-independence of **entire** unary
set-valued output fibres and the equality `p[F_new(q)] = F_old(p(q))`. Chart
closure and support monotonicity follow. Cyclic, branching and empty fibres
are allowed; no graph-pair-only surrogate for unary homomorphism is used.

`Sparsening/AtlasRecords` defines intrinsic quotient charge and exterior records.
Local agreement on true relation tuples and unary outputs is proved from their
contributing charts, rather than added as a hypothesis.

`Sparsening/AtlasSeparator` derives an actual common chart or proper closed-cut
certificate for a nonempty constant-charge test, hence for a chart-connected
test. The two sides cover the test, are proper and have exactly the stated root;
no true relation tuple crosses their exclusive parts. For a closed test,
closure is actual ambient closure, not just closure after omitting outside
outputs. The projected separator root is a closed old set contained in both
endpoint charts.

Earlier checked modules remain in use: `OddBoundary`, `StarCorrection`,
`ClosedCuts`, `RecordInvariance`, `ProjectionStep`, `CoherentTranslation`,
`Saturated`, `LocalParity` and `Descent`. The previous 90-declaration checkpoint
was source `c078ed47d096dfad1f4bb4d0c25efd187a2203de` (PR #11).

### Still pending

The full sparsening theorem is **not** yet formalized. The local atlas is generic
in a complete finite chart graph and closed chart membership; the proposed
application still has to instantiate the automorphism-invariant collection of
full copies and closed subcharts. Next are the affine action moving both the
ambient point and chart, full unary preservation, endpoint-extension/coherence
and transitivity. Then strict tree-amalgamation, irreducibility/faithfulness,
iteration and the final reduct must be assembled. The checked algebraic
cochain identity alone is not coherent EPPA.

Independent mathematical referee review of the full written proof remains
outstanding. Kernel checks and finite computational regressions are recorded
separately; neither is described as an independent referee's acceptance.

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

CI is adapted from `janhubicka/lean-successors`. GitHub Actions caches the pinned
toolchain and restores one shared pinned Lake workspace. Only a successful
`main` build after all proof/audit/regression gates pass seeds the large cache;
PRs reuse it but never upload per-PR copies. Artifacts retain commit IDs,
build/axiom logs, dependency inputs and SHA256SUMS. The generated untracked
manifest is omitted from the cache key because the dependency revision is
already pinned in `lakefile.toml`.
