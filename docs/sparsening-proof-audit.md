# Sparsening EPPA: statement correspondence and adversarial checklist

**Certified source:** merged Lean commit
[`136bd0f5f47209f090ea4e284a8c6a4c9386d795`](https://github.com/janhubicka/lean-gluing-eppa/commit/136bd0f5f47209f090ea4e284a8c6a4c9386d795).
Full PR CI [38738905840](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38738905840)
and merged-main CI [38739744079](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38739744079)
passed. The checked manifests comprise **331 named declarations** (281 + 21 +
12 + 17); all depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The three finite regression suites passed separately.

The target is Theorem 7.5 in the [2025 postprint of the Hubička–Konečný
survey](https://arxiv.org/html/2501.17293v5), **with a fixed language**.
Earlier versions of the survey use different theorem numbering.

## What the public types say

The hypothesis `[Finite B0]` provides a finite initial witness carrier.
`root : Set B0` is the distinguished induced copy of the original
`A`; `hr : UnaryClosed out0 root` means its full unary fibres are retained.
The public theorems also assume
`IsIrreducible (inducedRelations R0 root) (inducedUnary out0 root)`.
The initial EPPA hypothesis quantifies over **all**
`ClosedPartialAut`s of this induced root (not a selected partial-map
family).

`SparseningWitness R0 out0 root n` records one finite `B` with:

| Survey requirement | Formal field or lemma |
| --- | --- |
| Induced original root in `B` | `rootEmbedding : Tree.ExactUnaryEmbedding` |
| EPPA for all original partial maps | `extension`, `extension_spec` |
| Every irreducible closed test moved into the root | `faithful` |
| Homomorphism-embedding `B → B0` | `projection`, `projection_root` |
| Local bound through full-`A` tree amalgam | `local_trees`, `Tree.FullATree` |
| Coherent version from a coherent `B0` | `coherent_sparsening_eppa` |

`projection_root` states a stronger equality on the distinguished root.
The local target is a **strict** full-root tree, which is a tree amalgam
in the survey's sense when `A` is irreducible. The method does not assert
a globally injective projection or an induced map into a tree.

The ordinary existence theorem
`OrbitAtlas.sparsening_eppa` selects initial extensions from an input
EPPA-witness. The coherent theorem
`OrbitAtlas.coherent_sparsening_eppa` takes an actual coherent initial
family and constructs a *single* coherent witness satisfying the same
geometry. No result from `AllThoseEPPA.MainTheorems` is used.

## Short proof skeleton to audit

1. **One refinement.** Full closed subcharts of automorphic root images,
   with complete overlap graph and Boolean edge labels, yield an induced
   root chart and homomorphism-embedding projection. A closed test either
   lies in one chart or has a proper closed **upstairs** free cut.
2. **Bounded induction.** For a cut `X = X0 ∪ X1`, both old projected
   sides have at most `|Xi| < |X|` vertices. Glue their old target trees
   over the complete-`J` image of the *actual upstairs overlap*.
3. **Fixed root and extensions.** Exact root isomorphisms preserve the
   class of strict full-`A` trees, literally keeping the pushout maps
   unchanged. For each original partial map, its domain and range images
   are actual charts; the chosen extension sends the first chart **onto**
   the second. The two-spoke formula extends every map simultaneously.
   When the original family is coherent, its intermediate spoke cancels
   for every composable triple.
4. **Finish.** Iterate `m = max(1,n)` times. The composite projection
   fixes the original root, and one positive refinement guarantees
   faithfulness even when `n=0`. Forgetting `J` preserves free-cut
   witnesses, embeddings, strict trees and all chosen automorphisms.

## Adversarial failure modes excluded by the proof

- **Completing `J` at every stage:** this would destroy the sparsening
  geometry. Complete `J` is added **only initially**; later quotients
  retain their contributed relation.
- **Treating projected sides as a downstairs free cut:** even the
  inclusion `P4 → C4` preserves every edge and singleton exactly, but
  the extra endpoint edge ruins the old free decomposition. We always
  glue over the free cut in the actual upstairs test.
- **Confusing forward unary preservation with whole-fibre equality:**
  one-generated closure is irreducible, so local exactness forces
  equality of every entire fibre. This also yields closed image sets.
- **Assuming a merely embedded root is a full tree block:** the root
  map must be surjective onto the distinguished root. The proof uses
  `refinedRootExact_surjective` and `FullATree.changeBase`.
- **Using inverse-compatible extensions as coherent choices:** inversion
  alone does not imply the composition identity. The proof quantifies
  over all composable triples of original partial automorphisms.
- **Requiring global injectivity:** projections and local maps are only
  homomorphism-embeddings. They can identify nonadjacent vertices.
- **Forgetting edge cases:** the empty induced structure, nullary
  predicates, repetitions in relation tuples, unary cycles, and `n=0`
  are included.
- **Claiming induced local trees:** Boolean commuting valuation changes
  can retain an induced square, so only a homomorphism-embedding into a
  tree is claimed.

## How an independent referee can reproduce the checks

```sh
lake update
lake exe cache get
lake build
for manifest in scripts/Check*Axioms.lean; do
  log="${manifest%.lean}.log"
  lake env lean "$manifest" > "$log"
  python3 scripts/check-axiom-log.py "$log" "$manifest"
done
python3 scripts/check_saturated_cover.py --exhaustive
python3 scripts/check_atlas_action.py
python3 scripts/check_orbit_atlas.py
```

Those checks certify the declared Lean statements but do **not** establish
that the mathematical statement was encoded correctly; the table and
failure-mode checklist above are therefore separate obligations for
a human referee. We have carried out adversarial **self-audits**, not
independent mathematical refereeing.

The written TeX proof and manuscript validation markers belong in
[`janhubicka/Otto-simplified`](https://github.com/janhubicka/Otto-simplified),
not in this Lean library.
