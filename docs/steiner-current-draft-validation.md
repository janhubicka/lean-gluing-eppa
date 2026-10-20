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

## Target and fidelity rule

The target is `janhubicka/Otto-simplified`, `steiner_recursive_gluing_valuations.tex`.
The current self-contained revision is manuscript commit
`559401bee5aaa229875a837cb013797195f070b9`, source blob
`2ef757114e12e666144cecefbea53ce8fa1ec48f`.
It clarifies the component equality criterion, moves the right action before
its first use, shortens the injection and replacement arguments with that
criterion, and removes the optional proof importing an external theorem.
The construction, hypotheses, and theorem statements are unchanged.

Validate this construction, not merely its final EPPA conclusion. The older
Steiner PR #64 is a source of reusable elementary lemmas, not a certificate
for this draft. No old finite-group existence theorem is imported here.
All manuscript TeX remains in Otto-simplified.

## Checked foundation

Actions #302, run `39478304275`, completed successfully at Lean commit
`9b21d2ec1205b4d25b9c1ee71121f2d0bf5e18b0`. This includes the full build,
exact-name axiom audit, finite regressions, and structural audits.

- `WalkValues.lean` is reused unchanged for evaluation of actual named-edge
  walks. It supplies no recursion or synchronization premise.
- `CayleyLift.lean` defines literal steps `(u,g) -> (v,g*a_e)` and proves
  the exact lifted endpoint criterion `g^-1*h`.
- `CayleyComponents.lean` defines C_T from those actual walks, proves its
  equality criterion, finiteness, deck translations, and the right action
  `c(u,g) h = c(u,h^-1*g)`. Distinctness of marked components keeps the
  explicit value-one premise that the simultaneous induction must supply.

## Next submitted step

The following modules are submitted to CI, not certified by this ledger
until their build and exact-name axiom checks have passed. Current run
results are recorded in PR #65 and the manuscript validation ledger.

- `ComponentPermutations.lean`: the literal internal-translation/external-
  swap definition of tau_e^T; involutivity on the entire C_T; endpoint
  identity in both orientations; fixed points outside the marked pair;
  left-to-right word actions and concatenation; actual `WordWalk` witnesses,
  their equivalence with the old valued-walk interface, and endpoint action
  along a genuine walk.
- `ComponentInclusion.lean`: j_N^T as a map of actual component quotients;
  well-definedness from N subset T and an edge-preserving homomorphism;
  injectivity from the explicit earlier-stage property (II); preservation
  of marked components and equivariance under earlier-group translations;
  equivariance under both kinds of edge permutations and invariance of the
  image and its complement.
- `CheckComponentInclusionAxioms.lean` names all 22 new statements exactly.

The initial submission `2bba249cf8aeaa9bc3e8fe350cb17bd9fd7d331c` failed at
statement elaboration because transpositions need decidable equality before
the theorem proof begins. The repair supplies classical decidability at the
local declaration scope. This is not a new mathematical hypothesis or an
added axiom. No failed build is counted as validation.

## Remaining manuscript correspondence

| Current text | Status |
| --- | --- |
| Section 2: set-valued functions and closed Steiner systems | Reference infrastructure exists; current interface still to align |
| Section 3: inverse-paired binary edges | Adapter to named edges still open |
| Section 3: Boolean support lemma | Existing parity infrastructure; current interface still open |
| Section 4: actual lifts, components, equality criterion, deck action | Foundation checked by Actions #302 |
| Section 4: tau_e^T and endpoint action | New submitted component-permutation module |
| Lemma 4.1: j_N^T and its invariant image | New submitted component-inclusion module; exact earlier-stage hypothesis retained |
| Lemma 4.1: glue the two group actions on image and complement | Still open; image invariance alone is not the whole compatibility lemma |
| Theorem 4.2: direct-record simultaneous recursion and naturality | Still open for this draft |
| Remark 4.3 and Corollary 4.4 | Still open for this draft |
| Lemma 5.1: genuine closed induced Steiner free realization | Still open for this draft |
| Section 6: bipartite inclusion diagram and coherent EPPA | Still open for this draft |

The manuscript's comparison appendix is not a source of imported existence
results and has no new kernel certificate. Do not mark the main theorem or
the full recursion verified on the basis of these component lemmas.
