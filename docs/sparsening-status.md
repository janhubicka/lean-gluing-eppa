# Saturated Boolean sparsening: exact validation scope

The ordinary written proof is returned separately to the authors. No manuscript TeX is stored here.

## Target and method

The survey's `thm:hkn` includes irreducible-structure faithful EPPA, a homomorphism-embedding to a supplied witness, local homomorphism-embeddings to strict A-tree amalgams, unary functions, and preservation of coherent EPPA. The new proof development is restricted to the **relational, noncoherent** version. Inverse compatibility is not composition coherence.

Before each Boolean step take all automorphism-indexed copies of A in the previous witness and **all actual overlaps**. For each point u the resulting chart-support graph is complete. Its germ classes are exactly described by a boundary syndrome and the coordinates outside that support. Pairwise compatible such data admit one simultaneous chart: this is the new clique-containment argument. A local cut potential rules out a cycle with injective chordless projection. Consequently a nonchordal small image must lose vertices or gain an edge; a finite rank argument gives a chordal image, which embeds in a strict A-tree by fresh copies along a clique tree.

## What Lean checks in this PR

- Actual saturated overlap transport, its faithful frame, and relational compatibility.
- The ambient quotient projection is a homomorphism (global injectivity is NOT asserted).
- Local cut-potential invariance and cancellation around a closed walk.
- Strict finite descent from vertex loss or edge gain, with explicit numerical hypotheses.

The complete-support parity classification, affine clique-containment lemma, construction of the cut from an arbitrary induced cycle, geometric iteration and strict clique-tree completion are **not yet formalized**. The compiled rank uses m*(M+1)-e; the written note gives a tighter equivalent counting argument with binomial coefficients. Neither the full sparsening theorem nor the tighter iteration count is marked kernel-checked.

## Stronger local conclusion

Induced C4 rectangles survive this Boolean operator, already from A=K3 in B0=K4, and can be regenerated at every stage. Thus this particular iteration cannot replace the local homomorphism-embedding by an embedding. This is not a nonexistence theorem for stronger EPPA witnesses. The stronger relational conclusion has a separate black-box proof via Otto's corrected finite fully symmetric N-acyclic hypergraph-cover theorem (arXiv:1709.00031v3, Corollary 5.4); that theorem is not imported into Lean here.

## Actual checks

The mathematical adversarial passes were self-audits, **not independently spawned referee agents**. No external referee approval is claimed. `scripts/check_saturated_cover.py --exhaustive` compares a union-find quotient with a separate affine classification, searches maximal cliques and forbidden cyclic lifts, checks finite ranks, and supplies a persistent rectangle and a negative disconnected-support regression. These are finite tests, not substitutes for general proofs.

The first successful foundation build was at `257a63cd8479ac58b324380d71359ee4ba1bb9e8`, Actions run `38492918546`; later commits additionally run the finite regressions in shared-cache CI.
