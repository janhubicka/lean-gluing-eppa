# Validation of the current recursive gluing manuscript

## Validation scope and preservation

**Keep all existing validation of `amalgamation_diagrams.tex`.** The relational
EPPA, complete-overlap sparsening, and coherent results remain an active part
of this library. Preserve all supporting Lean modules, declarations,
exact-name axiom manifests, regression tests, CI coverage, manuscript markers,
and pinned proof references. The new Steiner proof does not replace that
validation. Do not remove those dependencies or checks when cleaning up
superseded Steiner work.

The only active Steiner manuscript target is
`janhubicka/Otto-simplified/steiner_recursive_gluing_valuations.tex`.
The other Steiner notes and the earlier proof in PR #64 are superseded as
validation targets; completing their separate formalizations is not required.
Retain their sources and useful counterexamples or elementary lemmas as
reference material. Reuse is allowed only when it matches the current draft
or after proving the necessary correspondence. Existing proofs and checks
are not deleted by this scope decision, and no earlier result is declared
false merely because its manuscript is no longer a target.

## Target and fidelity

The current self-contained source is manuscript commit
`559401bee5aaa229875a837cb013797195f070b9`, blob
`2ef757114e12e666144cecefbea53ce8fa1ec48f`.
Validate its actual construction, not merely the same EPPA conclusion.
No old recursive-group existence theorem or external acyclicity theorem
is imported. All manuscript TeX remains in Otto-simplified.

The proof-code snapshot and completed run results are recorded in
[PR #65](https://github.com/janhubicka/lean-gluing-eppa/pull/65) and in
[the manuscript ledger](https://github.com/janhubicka/Otto-simplified/blob/main/STEINER_VALIDATION.md).
Do not infer successful validation merely from a submitted source file.

## Previously checked foundation

Actions #304, run `39488815380`, passed completely at
`2ec0ccc535a397c1383a541f85301865b7c4869a`.
It checked all earlier declarations and both component manifests (18 + 22
names), finite regressions, import coverage and wiki links.

- `WalkValues.lean` is elementary reused evaluation of actual named-edge walks.
- `CayleyLift.lean` defines literal lifted steps and exact endpoint value g^-1*h.
- `CayleyComponents.lean` defines the finite quotient by actual connectivity,
  its equality criterion, deck translations, and inverse-left-translation
  right action. Marked-component injectivity retains the earlier value-one premise.
- `ComponentPermutations.lean` defines internal translations/external swaps
  on every component, involutivity, arbitrary-word composition, and actual-walk
  endpoint identities.
- `ComponentInclusion.lean` defines j_N^T, proves it injective under the exact
  earlier replacement premise, and proves translation and generator equivariance
  and invariance of its image and complement.

## Current construction modules and exact correspondence

The new modules are checked by `CheckComponentCompatibilityAxioms.lean`
(18 exact names), `CheckRecordValuationAxioms.lean` (18), and
`CheckRecordInclusionAxioms.lean` (10). The latest completed run, rather than
this list of files, determines their checked status.

### Lemma 4.1: actual actions on both parts

`RightAction.lean` proves the identity and multiplication laws for an action
transported to the image of an injection, combined with an action on its
invariant complement. Invariance is under the whole group, not just generators.

`ComponentCompatibility.lean` applies this to the actual map j_N^T. On its
image it uses the old K_M coordinate action on C_N; outside it uses the deck
action through i_N^T composed with r_N^M. It proves the named-generator rule
on all of C_T, then preservation of every old word equality, without requiring
those words to be walks. The nested-subset case is also proved.

Earlier replacement in the smaller T-lift, the deletion map, and the smaller
coordinate action remain explicit induction inputs. Their existence is not
silently assumed as a theorem about the completed recursion.

### Literal new valuation and image group

`RecordValuation.lean` defines exactly the word record in the product of old
groups and old component permutation groups. Opposite permutation multiplication
implements the manuscript's left-to-right convention. It proves multiplication,
reversal, the image-subgroup construction, finiteness, and involutive generators.
Deletion is the first-coordinate projection. Its surjectivity is proved before
the new inclusion, using only earlier word representations. The component
coordinate is an actual right action with the required generator rule.

### Inclusion and exact replacement

`RecordInclusion.lean` combines the group-coordinate maps and compatible
actions into a product homomorphism. It constructs the inclusion into the
literal image subgroup using word representations, proves its word formula,
and proves that projection is a left inverse, hence injectivity.

`inclusion_componentAction` derives its own smaller-component coordinate from
the generator rule. `inclusion_replacement` then proves property (II) for this
actual inclusion, by extracting a walk from c(u,g^-1) = c(v,1). It does not
assume the new replacement property or an additional coordinate-action premise.

## What remains

The one-stage construction results are not yet an unconditional finite-family
existence theorem. The simultaneous induction must still instantiate the old
data for all proper subsets, compose the maps coherently, and prove naturality.
The actual binary-language edge adapter and the Boolean interface remain open,
as do final exact intersections, the closed induced Steiner realization,
the bipartite inclusion diagram and the unconditional coherent EPPA theorem.
The appendix comparison lemmas have no new kernel certificate here.

No main-theorem or full-recursion validation marker follows merely from the
conditional one-stage lemmas. Continue with the current direct-record family,
not the superseded proof. All amalgamation-diagram tests remain active.
