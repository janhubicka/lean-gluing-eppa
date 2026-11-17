# Verified-source two-block M-edge reflection package

These ten modules are byte-for-byte identical to Git blobs at old
PR #152 head `811216a44a6cc049543362711dfb0009a9e140f1`.
That run (42481896395) compiled `NormalizedTwoBlockComponent`
and `NormalizedTwoBlockEdges`, while failing only in the separate
`MatchedComponentChartExtension` subtype injection lemma.

This integration is stacked on repaired generic chart PR #175,
and must pass a NEW exact-head full Lean build and named axiom audits
before any merge.

The substantive end result is `normalized_twoBlock_genuine_edge_iff`:
the normalized two-block smaller-mask pushout reflects and preserves
EVERY genuine e-edge for e∈M of the literal original two-block Link
quotient on the selected component. This uses exact restricted
Cayley coset equivalences, the whole matching interface and exact
pushout edge reflection, not a mere surjective graph map.

The checked general theorem `matching_family_perm_equivariant` then
explains mathematically why **two-way edge reflection** is the right
hypothesis for the completed letter permutations, including fixed
points. The *all-length* extension to an arbitrary finite separated
chain is still open and is NOT claimed by this package.

No manuscript or verified Part I files are touched.
