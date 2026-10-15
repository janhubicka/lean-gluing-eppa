# Using the Gluing EPPA Lean library

## Install and import

Pin a tested source revision in a compatible Lean 4 project:

~~~toml
[[require]]
name = "gluing-eppa"
git = "https://github.com/janhubicka/lean-gluing-eppa"
rev = "136bd0f5f47209f090ea4e284a8c6a4c9386d795"
~~~

The checked source pins `leanprover/lean4:v4.35.0-rc3` and Mathlib
`5bd58ac291422a21f412ae354c91e7d172255a2c`. Downstream projects
should test their own toolchain/Mathlib compatibility and run `lake build`.
There is no special code-generation step.

~~~lean
import GluingEPPA

#check GluingEPPA.finite_relational_eppa_private
#check GluingEPPA.Sparsening.OrbitAtlas.sparsening_eppa
#check GluingEPPA.Sparsening.OrbitAtlas.coherent_sparsening_eppa
#check GluingEPPA.Sparsening.OrbitAtlas.SparseningWitness
#check GluingEPPA.Sparsening.ClosedPartialAut
#check GluingEPPA.Sparsening.IsIrreducible
#check GluingEPPA.Sparsening.Tree.UnaryHomEmbedding
#check GluingEPPA.Sparsening.Tree.ExactUnaryEmbedding
#check GluingEPPA.Sparsening.Tree.FullATree
~~~

All names above are real library declarations, not proposed new APIs.
Importing a narrower module is also supported, e.g.

~~~lean
import GluingEPPA.Sparsening.SparseningTheorem
import GluingEPPA.Sparsening.UnaryGeneratedClosure

#check GluingEPPA.Sparsening.OrbitAtlas.sparsening_eppa
#check GluingEPPA.Sparsening.Tree.UnaryHomEmbedding.out_eq
~~~

## Basic representation

`GluingEPPA.RelStructure L A` interprets an arity-indexed relational
language `L : Nat → Type`. Unary functions are separately represented as
`F → A → Set A` and may be empty, branching or cyclic. A
`UnaryClosed` subset contains **the entire** output of every vertex in
that subset. The induced structure is defined only on a closed set when
used as a genuine substructure.

`Tree.ExactUnaryEmbedding` means an **injective** map reflecting and
preserving all relations and mapping each *whole* unary fibre **onto**
the corresponding target fibre. The reusable
`Tree.UnaryHomEmbedding` is exact on each closed irreducible induced
test, but need not be globally injective; such maps compose.

The checked lemma `Tree.UnaryHomEmbedding.out_eq` says that local
exactness itself forces the full-fibre equality: generate the smallest
closed substructure containing a vertex and observe it is irreducible.
This also proves closed images for every closed source set. Do not
replace whole-fibre equality by forward membership alone.

`IsIrreducible` is **absence of a free decomposition into two proper
closed induced substructures**; it is not just absence of a graph cut.

## Applying the sparsening theorem

`SparseningWitness R0 out0 root n` packages **one finite** output
structure carrying all the needed conclusions. The inputs are an
original finite ambient witness `B0`, an induced **closed** copy
`root` of the original irreducible structure, an ordinary input
EPPA condition quantified over **all** closed partial automorphisms
of the root, and a bound `n : Nat`.

The output carries an exact root embedding, one extension family,
irreducible-structure faithfulness, a root-fixing projection to
`B0` which is a homomorphism-embedding, and finite strict full-root
tree targets for every closed test of at most `n` vertices.

Use `OrbitAtlas.sparsening_eppa` for the ordinary existence theorem.
For the stronger coherent conclusion, supply an initial
`OrbitAtlas.CoherentFamily` and use
`OrbitAtlas.coherent_sparsening_eppa`.
Coherence means a composition equation **for every composable triple**
whose middle range equals the next domain; inverse-compatible choices
alone are not enough.

## Reusing smaller components

| Import | Mathematical purpose |
| --- | --- |
| `GluingEPPA.Sparsening.TreeHomEmbedding` | Locally exact homomorphism-embeddings and composition |
| `GluingEPPA.Sparsening.UnaryGeneratedClosure` | Generated closures, full fibres, closed image |
| `GluingEPPA.Sparsening.TreeFullA` | Strict free-amalgamation trees of full base copies |
| `GluingEPPA.Sparsening.TreeBaseChange` | Change of base along an exact isomorphism |
| `GluingEPPA.Sparsening.OrbitFiniteTower` | Finite iteration and fixed-root local bounds |
| `GluingEPPA.Sparsening.OrbitTowerReduct` | Forgetting the auxiliary J and faithfulness |
| `GluingEPPA.Sparsening.ClosedPartialAut` | Closed partial maps and actual matched-domain composition |
| `GluingEPPA.Sparsening.OrbitExtensionFamily` | Extension-family transport and coherent cocycle |
| `GluingEPPA.Sparsening.SparseningTheorem` | Simultaneous ordinary and coherent theorem |

The public umbrella `GluingEPPA` includes the ordinary finite
relational EPPA development alongside sparsening. The source also has
finite unordered-edge and private-marker extensions, recorded in
[Finite relational EPPA](Finite-relational-EPPA.md).

## Reproducing the kernel audit

~~~sh
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
~~~

Only `propext`, `Classical.choice`, and `Quot.sound` appear among
the audited axioms. The Python regressions are supplementary and
are not part of the kernel proof. See [Development and audit](Development-and-audit.md).
