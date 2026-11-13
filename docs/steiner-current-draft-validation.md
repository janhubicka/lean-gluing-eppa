# Validation of the current recursive gluing manuscript

## Scope and preservation

**Keep all existing validation of `amalgamation_diagrams.tex`.** Its relational
EPPA, complete-overlap sparsening, and coherent results remain active. Preserve
their Lean modules, exact-name axiom manifests, regressions, CI checks,
manuscript markers, and pinned proof references. No such proof or check is
removed by the current Steiner work.

The only active Steiner manuscript target is
`janhubicka/Otto-simplified/steiner_recursive_gluing_valuations.tex`.
Other Steiner notes and PR #64 are superseded as validation targets, not
sources to delete or results to declare false. Reuse elementary results only
when they match this proof or after proving the necessary correspondence.

## Target and evidence

Manuscript source: `559401bee5aaa229875a837cb013797195f070b9`, blob
`2ef757114e12e666144cecefbea53ce8fa1ec48f`.
This pass changes no TeX, hypotheses, or theorem statement.
All manuscript TeX stays in Otto-simplified.

The checked proof-code snapshot and full-run evidence are recorded in
[PR #65](https://github.com/janhubicka/lean-gluing-eppa/pull/65) and
[the manuscript ledger](https://github.com/janhubicka/Otto-simplified/blob/main/STEINER_VALIDATION.md).
A source file or a failed/interrupted run is not a certificate.

Checked proof-code commit: **`a6d94ac21ee22bd7958bc0bbb6fc3f71fa71744f`**.
[Actions #316](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/39511924460)
passed the full build, every exact-name axiom audit, existing regressions,
import coverage and wiki checks. The downloaded artifact has SHA-256
`1c93e6bb2815689ac3ed0fca21b62b882369280837bb28d3180dd12d5d480bbd`;
all 23 internal hashes were verified. Its test-merge commit is
`ff6c4ac90434bf449dc3237f64515126c720790b`.

The three new manifests check 53 exact names (17 + 19 + 17), with only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, custom axiom,
or untrusted evaluation occurs. The same run checks 470 outputs in total,
including all 331 original amalgamation/sparsening checks and the 86 earlier
current-draft checks. All 100 source modules remain covered.
This documentation update does not change the checked proof sources.

## Correspondence with the current proof

### Actual components and one construction step

`CayleyLift`, `CayleyComponents`, `ComponentPermutations`, and
`ComponentInclusion` define the actual lifts, their finite component sets,
the internal-translation/external-swap permutations, and j_N^T.
`RightAction` and `ComponentCompatibility` construct both invariant-part
actions and verify every old word equality on the entire component set.
`RecordValuation` defines the literal product record and its image subgroup.
`RecordInclusion` constructs the new inclusion, derives its component action,
and proves the one-stage exact replacement conclusion.

These were checked at `cd1a3fe513cb1e52e5f0105fe8fedae0da85de39` in
Actions #311. The earlier-stage premises in those modules are now supplied
by the recursive construction below; they are not global assumptions.

### RecursiveRecord: construct the actual groups first

`RecursiveRecord.family` is well-founded recursion on the cardinality of S.
Its equation constructs the same literal record image from this family's
values at all proper subsets. No alternate family of groups is selected.
Finiteness, involutive named generators and allowed-word representations
are proved during construction. The empty-stage record is an empty product
and is proved trivial. Outside S the total generator function is 1; all
walks and representation words retain their stated edge restriction.

`Step.action` is precisely the old component-coordinate projection.
`family_coordinate_action` obtains it by unfolding the actual earlier
record; it is not an additional assumption of the compatibility lemma.

### RecursiveLinks: supply the simultaneous induction

`Link` packages inclusion, deletion, their generator rules, and exact
restricted-walk replacement. It is the induction target, not assumed data
about the final family. `family_links` constructs it for every M subset S
by strong induction. All links used at a new stage have proper smaller
targets; in the crossing case N = M intersection T is proper in M, so the
required C_N coordinate really exists in the old K_M record.

The complete K_M-action is then assembled from the already checked two-part
construction. `Step.link` uses the literal product inclusion and coordinate
deletion, and invokes the derived component-action formula to obtain (II).
No new-stage replacement or compatibility hypothesis is supplied.

### RecursiveTransport: coherent maps and actual endpoint intersections

`Data.hom_ext` proves uniqueness of homomorphisms from named generators.
The selected links therefore give the constructed maps on fixed carriers,
not substitute groups. Retraction, inclusion injectivity, and composition
of successive inclusions and deletions are proved.

`replacement` is (II) with no earlier-stage premise left over. The
commuting projectors are proved on the actual final group. A common value
of two restricted walks is fixed by the intersection projector; deletion
supplies its smaller preimage, replacement produces an actual restricted
walk, and inclusion restores the full value. `exact_intersection_walk`
retains both original lifted endpoints. `component_intersection` gives the
binary component-set equality in the literal final lift.

The ambient group is never changed when allowed edges are restricted.
No nonemptiness restriction on base vertices or component parts is added.

## Proof boundary and next targets

The core finite-subset recursion and binary exact intersections are proved
for named loopless graphs with parallel edge names allowed. The formal adapter
from the manuscript's inverse-paired binary relations remains to be supplied.
Edge subsets use `Finset E`, with E finite; the set-notation and nonempty
finite-family corollary wrappers are also still to add.

Naturality under diagram isomorphisms is **not** a consequence already checked
by `family_links`. It must be proved for this same literal family, including
symmetries which reverse an undirected edge. Next: component isomorphisms,
conjugation of edge actions, reindexing of record coordinates, restriction to
the image groups, and identity/composition from the generator equations.

The Boolean quotient interface, the actual closed induced Steiner free
realization, the relabelled bipartite inclusion diagram and the final coherent
EPPA theorem remain outstanding. The comparison appendix has no new certificate.
Do not mark all of Theorem 4.2 or the main EPPA theorem verified on the basis
of the core recursion. No older recursive-group theorem or Otto existence
theorem is imported; only elementary actual-walk evaluation is reused from
the superseded Steiner work.
