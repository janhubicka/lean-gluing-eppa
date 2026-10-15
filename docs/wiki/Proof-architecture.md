# The proof architecture, without Lean syntax

The proof separates **permutation extension** (EPPA) from
**geometric control** (sparsening). Both parts use gluing diagrams, but
different layers of the Lean library handle their arguments.

## 1. Ordinary relational EPPA

Given a finite relational `A`, choose a finite family of partial
automorphism labels and extend them by permutations on a padded carrier.
The permutation diagrams guarantee the compatibility of directed
and unordered edges and their inverses. A Boolean valuation is attached
to each appropriate base-edge occurrence. Gluing chart copies along
labelled edges produces a quotient which preserves and reflects relation
tuples on the distinguished copy of `A`.

The **private-marker** refinement uses two- and three-cycle markers,
ensuring the desired permutations and inverses extend without collapsing
the distinguished structure. The checked final output is
`finite_relational_eppa_private`. This theorem proves EPPA for all
finite structures over fixed finite relational languages without assuming
an earlier EPPA witness.

## 2. Add a genuinely binary auxiliary relation

For sparsening, start with an irreducible closed `A` inside a finite
EPPA witness `B0`. Add a new binary relation `J` interpreted as
**complete on the entire initial `B0`**. This changes none of its
automorphisms or the partial automorphisms of `A`.
Later stages retain the `J` relation **contributed by the charts**;
they do not complete it again.

The point of `J` is not cosmetic. A complete `J` set is irreducible,
so an overlap mapped into a tree target lives inside a full building
block. This permits literal strict tree gluing.

## 3. Every closed subchart participates

In each stage `C`, designate one induced closed root `A_C`.
Its **full charts** are the automorphic images `h[A_C]`;
the chart family contains every **closed subset** of every such image,
including the empty set. These are actual subsets, not chart
presentations indexed by embeddings.

The graph on chart indices is the complete loopless graph. Give each
edge an independent Boolean coordinate. For every actual common
point `x ∈ s ∩ t`, identify
`(s,chi,x)` with `(t,chi+1_{s,t},x)`.
Quotient vertices are supported equivalence classes of triples, so
nonexistent chart occurrences are never introduced. Relations and unary
fibres are exactly those contributed by the charts; the canonical
projection sends `[s,chi,x]` to `x` and is a
homomorphism-embedding on irreducible closed tests.

## 4. The geometry: chart or real free cut

For a closed upstairs test `X`, a parity/exterior-coordinate argument
gives two alternatives: either all of `X` lies in a single lifted
chart, or `X` has a genuine **free decomposition upstairs** into
two proper closed induced sides. The projected overlap is a closed
`J`-complete set in the preceding stage.

The difficult rule is what **not** to infer. The projected sides need
not form a free decomposition downstairs: old structures can have
additional tuples absent upstairs. The proof never makes this leap.

If `|X| ≤ k+1`, both proper upstairs sides have at most `k`
vertices; their old projected images have no more vertices than
their sources. The induction hypothesis gives two finite full-root
tree targets. Since their projected common overlap is `J`-complete,
each attaching map factors through an actual full-root block.
We glue the target trees along those maps, using the real upstairs
cut to establish the homomorphism-embedding conclusion.

This proves the checked bounded one-step lemma and, by induction,
the local-tree conclusion at every finite stage.

## 5. Keep the same actual root throughout

The distinguished full zero-valuation chart of each refinement is an
**exact surjective** copy of the preceding root; it is closed and
`J`-complete. An isomorphism `e : A → B` induces the same
strict-tree class: replace a gluing interface `delta` by
`e⁻¹ ◦ delta` and the copy map `alpha` by `alpha ◦ e`.
Their composition remains `alpha ◦ delta`, so the actual
pushout target is unchanged.

This is more precise than saying merely that two tree classes
are somehow equivalent. It allows all local targets to use the
**original** `A` as the building block while quotient stages grow.

## 6. All partial maps and coherence move together

Keep **one fixed index set**: every partial automorphism of the
original closed `A`. At stage `i`, its exact root embedding
maps each original closed domain and range to actual chart subsets.
The chosen old extension maps the domain image **onto** the range
image; surjectivity of the partial isomorphism is essential.

The extension at the next stage is the affine **two-spoke** lift
between these domain and range charts. For a composable triple
`f,g,h=g∘f`, the intermediate chart is the same on both sides,
and the corresponding spoke terms cancel. The quotient action
then gives `H(h)=H(g)∘H(f)` for every such triple. This is
the genuine coherent EPPA law, not merely inverse compatibility.

## 7. The final single witness

Perform `m = max(1,n)` refinements. The composite projection
back to `B0` is a homomorphism-embedding and fixes the original
root under its exact embedding. One positive stage gives
automorphic faithfulness, including the `n=0` case.
The numerical induction gives finite full-`A` trees for all
closed tests of at most `n` vertices.

Forget `J`. The same vertex set, functions, extension family,
tree targets and projection remain valid in the original language.
The full witness record ensures these are not unrelated existential
choices. The ordinary/coherent endpoint theorems conclude.

The [sparsening construction page](Sparsening-construction.md)
identifies the Lean modules at each step. For the exact
assumptions, consult [Published statements](Published-statements.md).
