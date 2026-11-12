# Part II chain valuations: equivariant covers rather than component isomorphisms

**12 November 2026.** Scope: inclusion property (a) for the recursive
valuation family in `Otto-simplified/part_ii_chain_valuations.tex`.
This is a mathematical proof-reduction and Lean source draft, **not**
a new proof of the chain-restriction lemma or of N-acyclicity.

## Kernel-transfer statement

Fix the alphabet M and an M-letter permutation family τ on a test X.
For indexed earlier tests Y_j with M-letter permutations σ_j, suppose
maps f_j:Y_j→X satisfy

    f_j(σ_j(e,y)) = τ(e, f_j(y))  for every e∈M, j, y,

and their images jointly cover X. Induction on an M-word w gives

    f_j(σ_j(w,y)) = τ(w, f_j(y)).

Consequently, for M-words p,q, if σ_j(p)=σ_j(q) on **every** Y_j,
then τ(p)=τ(q) on X: choose a preimage of an arbitrary x∈X
and transport the equality. **No injectivity of f_j** is needed.

This is the actual implication used to carry property (a) to a
new chain test. It is formalized, as a Lean proof candidate, in

    GluingEPPA/Steiner/ChainValuation/EquivariantTestCovers.lean

with the two declarations

    testWordPerm_map_of_generator_intertwining
    testWordPerm_eq_of_joint_equivariant_cover.

These are registered in `scripts/CheckChainValuationAxioms.lean`.
The code is not compiled at this checkpoint.

## Geometric obligation which remains

We still need to produce, for **every actual M-component** in a
separated chain test of length ≤N, an indexed family of smaller
recorded tests covering that component by maps intertwining the
**completed M-letter permutations**. The earlier theorem candidate
`lem:chain-restriction` gives a stronger isomorphism onto either a
full K_M block or a normalized proper chain; such an isomorphism would
supply the cover immediately.

The existing generic `pushoutMap_surjective` theorem is useful
for constructing covers inductively but is *not* sufficient alone:
its functorial map does not automatically intertwine all completed
letter permutations. One also needs compatibility of the actual
M-edges and **reflection of unmatched fixed points**.

### Negative control

A one-point source on which e acts as the identity can map to one
endpoint of a two-point target on which e swaps the endpoints.
This map vacuously preserves all *positive e-edges* in the source,
but it does **not** intertwine completed e-actions. Covering all
target points by such maps would still not transfer word kernels.
Therefore plain surjective positive-edge graph morphisms are
insufficient; the full equivariance hypothesis cannot be silently
dropped.

## Relation to the manuscript proof

The manuscript itself says the restricted components are covered
by regular K_M diagrams and recorded separated-chain tests, with
maps preserving all M-letter transitions. The last implication
uses *surjectivity*, not bijectivity. Hence it is legitimate to
attempt a weaker, cover-first formalization of property (a)
without changing the theorem statement.

However, the stronger `lem:chain-restriction` remains an independently
stated claim with an unresolved all-length normalization proof.
Even if a cover-first argument eventually proves property (a),
it does not by itself validate the stronger lemma, the bounded
coset-cycle unwinding, the reflection-of-intersections theorem,
the naturality construction, or the Part II main theorem.

The manuscript and previously verified Part I remain unchanged.
