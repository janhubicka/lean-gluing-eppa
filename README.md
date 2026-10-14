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

## Sparsening: local geometry and generic affine action checked

The library now passes a **132-declaration axiom audit**. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted; no `sorryAx` or custom
assumed axiom occurs in the audited declarations' transitive dependencies.
**The full sparsening theorem remains pending.**

- PR #12, source `97f834c6639e0b2948d6c641323318bfb6e3e261`, added the actual
  supported-walk converse, valid variable-size chart quotient and full unary
  fibres. Run `38503255935` passed all gates with 106 audited declarations;
  merged as `24f429e4adaa512efb40e384e7de8977a15ae8fe`.
- PR #13, source `9216dcc8a72e7d69067395f90de7c988b740aabb`, derived the concrete
  chart-or-closed-separator certificate. Both PR run `38503944598` and the
  merged-main run `38504321125` passed all gates with 119 audited declarations.
- PR [#14](https://github.com/janhubicka/lean-gluing-eppa/pull/14), source
  `2947c28fdd2996e3348375c64d3da52b2db3196d`, added the generic affine quotient
  action, full unary-fibre preservation, supported endpoint extensions,
  quotient-level composition/identity and exact chart image equations.
  [PR run](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38565510278)
  and [merged-main run](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38567430312)
  passed the full build, **132-declaration audit**, existing regressions and
  new union-find affine-action regressions. Merged mathematical source:
  `b4c2a22c28de7a4635beed161a6e930a2991232e`.

### Checked local geometry

`Sparsening/CompleteRecords` constructs supported walks by concatenating rooted
excursions and an endpoint spoke. Equality of pointed boundary charge and of
exterior coordinates is equivalent to path equivalence on valid occurrences.
Disconnected parity support, loops, parallel edges, singleton supports and
zero-length walks are included. Completeness and endpoint membership are
explicit hypotheses, not implicit connectivity assumptions.

`Sparsening/ChartAtlas` forms the quotient only from triples `(s,chi,x)` with
`x ∈ s`. Its fibrewise presentation contains no artificial outside-chart
vertices. Canonical charts are induced embeddings; complete records and star
correction give an actual common lifted chart.

`Sparsening/UnaryAtlas` proves representative-independence of entire unary
set-valued output fibres and `p[F_new(q)] = F_old(p(q))`. Cyclic, branching,
empty and self-containing output sets are allowed.

`Sparsening/AtlasRecords` supplies intrinsic quotient records and derives local
agreement on relation tuples and unary outputs from their contributing charts.
`Sparsening/AtlasSeparator` derives actual chart containment or a proper closed
cut for nonempty constant-charge tests. For a closed test the sides are ambient
closed, and the projected root is closed and contained in the endpoint charts.

### Newly checked affine action and endpoints

`Sparsening/AtlasAction` moves both the ambient point and its chart. Membership
and incidence equivariance are its elementary geometric inputs; it proves
supported-walk descent, a quotient equivalence with explicit inverse, relation
preservation/reflection, and composition on quotient vertices:

    L(g,epsilon) L(h,delta) = L(gh,epsilon + g_*delta).

`Sparsening/AtlasUnaryAction.map_output_image` proves equality of whole unary
output sets under the action, using explicit old unary-automorphism and closed
chart hypotheses. This is not merely a graph-pair homomorphism check.

`Sparsening/AtlasEndpoint` constructs uniform root spokes from graph
completeness. With correction `eta_R + (h_f)_*eta_D`, it proves the actual
quotient extension equation by two supported spokes. It also proves endpoint
composition/identity on quotient maps and exact images of entire charts.
Arbitrary source/target valuations can be matched by a translation once the
old chart movement is supplied. These are generic action results, not an
assumed upstairs EPPA or local-tree property.

`scripts/check_atlas_action.py` builds finite quotients independently by
union-find, not by record classification. It checks 712 actions on 9,984
valid occurrences, 258,048 full unary fibres and inverse/composition equations,
and detects two deliberately broken rules in each of three cases. The JSON
result is retained in every proof artifact. Finite checks are supplementary,
not replacements for general Lean proofs.

Earlier modules remain in use: `OddBoundary`, `StarCorrection`, `ClosedCuts`,
`RecordInvariance`, `ProjectionStep`, `CoherentTranslation`, `Saturated`,
`LocalParity` and `Descent`.

### Still pending

The automorphism-invariant family of full copies and closed subcharts must be
instantiated, with its canonical chart/edge action shown to compose. The new
generic equations then have to be packaged into coherent lifted extensions and
transitivity on full copies. Strict tree-amalgamation, irreducibility and
faithfulness, iteration and the final reduct are not yet assembled.
The quotient endpoint identity alone is not the full coherent sparsening theorem.

Independent mathematical referee review of the written proof remains
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
already pinned in `lakefile.toml`. PR #14 leaves this caching policy unchanged;
it adds the affine regressions to the existing finite-test gate.
