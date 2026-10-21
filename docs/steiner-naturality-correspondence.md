# Current-draft naturality and finite intersections

Target: `Otto-simplified/steiner_recursive_gluing_valuations.tex`, source
commit `559401bee5aaa229875a837cb013797195f070b9`.
This document describes proof correspondence, not a separate certificate.
The successful source snapshot and exact-name axiom results must be pinned
in PR #65 and the manuscript's `STEINER_VALIDATION.md`.

## Preserve the construction and earlier validation

All validation of `amalgamation_diagrams.tex` remains active. The full library
build, all existing axiom manifests, regressions and structural checks remain
in the workflow. The older Steiner notes are not separate validation targets.
No external acyclicity theorem or superseded recursive-group theorem is used.

## Naturality paragraph before Theorem 4.2

`CayleyIsomorphism.lean` defines named-edge isomorphisms using undirected
incidence. In particular it does not assume that the chosen source and target
of each named edge are preserved. It maps actual Cayley walks in both directions,
constructs the component equivalence from that actual connectivity quotient,
and proves conjugacy of deck translations and external swaps. The external
case explicitly treats both endpoint orientations. Conjugacy propagates to
arbitrary words, not only words labelling walks.

`WordHomomorphism.lean` is elementary generated-group infrastructure. It proves
independence of chosen word representatives under an explicit equality-
preservation hypothesis; that hypothesis is discharged in the next modules.
This does not construct substitute groups or assume symmetry of the new record.

`RecordIsomorphism.lean` compares every coordinate of the actual record.
Old-group coordinates commute with deleting letters. Old-component coordinates
are conjugated by the preceding equivalence. Every target proper-subset
coordinate is compared with its actual source proper subset. Preservation of
new word equalities is a conclusion, not a hypothesis.

`RecursiveNaturality.lean` supplies those smaller isomorphisms by strong induction
for the same `RecursiveRecord.family`. The new isomorphisms have the precise
generator rule. Homomorphism uniqueness on generators then proves identity,
composition and commutation with inclusion and deletion. The resulting maps
preserve actual restricted walks with both endpoints specified.

## Corollary 4.4

`FiniteIntersections.lean` converts the binary finite-set statement to arbitrary
edge subsets, and iterates it over a nonempty finite index set. The ambient final
group and both endpoints remain unchanged. Nonemptiness is retained explicitly;
the empty intersection would be the entire vertex set, not a connected component.

## Boundary

These statements are still at the named loopless-edge-graph interface, where
parallel edge names are allowed. The inverse-paired binary-language adapter,
Boolean quotient, actual point quotient with closed Steiner embeddings,
labelled bipartite inclusion diagram and unconditional coherent EPPA theorem
must still be completed. A current-draft theorem marker requires its entire
interface and all its conclusions, not merely these graph-level ingredients.
