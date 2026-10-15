# Gluing EPPA — a verified Lean 4 research library

A reusable, kernel-checked formalization of **finite relational EPPA by
gluing diagrams** and **complete-overlap sparsening EPPA** for
structures with relations and whole set-valued unary functions.

**[Research wiki](docs/wiki/README.md)** ·
[Using the library](docs/wiki/Using-the-library.md) ·
[Published-statement crosswalk](docs/wiki/Published-statements.md) ·
[Proof architecture](docs/wiki/Proof-architecture.md) ·
[Auxiliary lemmas](docs/wiki/Auxiliary-lemmas.md) ·
[Adversarial referee audit](docs/wiki/Adversarial-referee-record.md)

The [GitHub Wiki tab](https://github.com/janhubicka/lean-gluing-eppa/wiki)
is synchronized from version-controlled `docs/wiki/` after its separate
Wiki Git repository has been initialized. Until then, the source pages
linked above are the fully readable documentation. Publication details
are in [Publishing](docs/wiki/Publishing.md).

## The two main results

The unconditional finite relational theorem constructs a finite induced
EPPA-witness for any finite structure over a fixed finite **relational**
language. It covers nullary relation symbols, repeated tuple coordinates,
and the empty partial automorphism.

The sparsening theorem begins with a finite EPPA-witness `B0` for a
finite **irreducible, closed** distinguished `A` and a bound `n`.
It gives **one finite witness** that is irreducible-structure faithful,
has a root-fixing homomorphism-embedding back to `B0`,
and maps every closed test of at most `n` vertices by a
homomorphism-embedding into a finite *strict* full-`A`
tree amalgam. If the initial witness has coherent extension choices,
the constructed witness has coherent extension choices as well.

The ordinary/coherent sparsening results are checked at merged revision
[`136bd0f5`](https://github.com/janhubicka/lean-gluing-eppa/commit/136bd0f5f47209f090ea4e284a8c6a4c9386d795):
[PR CI 38738905840](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38738905840)
and [merged-main CI 38739744079](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38739744079)
both passed. Across four named manifests, **331 Lean declarations**
were audited; only `propext`, `Classical.choice` and
`Quot.sound` occur in their transitive axiom dependencies.

~~~lean
import GluingEPPA

#check GluingEPPA.finite_relational_eppa_private
#check GluingEPPA.Sparsening.OrbitAtlas.sparsening_eppa
#check GluingEPPA.Sparsening.OrbitAtlas.coherent_sparsening_eppa
#check GluingEPPA.Sparsening.OrbitAtlas.SparseningWitness

-- Import a narrow reusable mathematical interface instead if desired.
#check GluingEPPA.Sparsening.Tree.UnaryHomEmbedding
#check GluingEPPA.Sparsening.Tree.ExactUnaryEmbedding
#check GluingEPPA.Sparsening.Tree.FullATree
#check GluingEPPA.Sparsening.Tree.UnaryHomEmbedding.out_eq
~~~

## Reuse and installation

Pin a tested revision in a compatible Lean 4 Lake project:

~~~toml
[[require]]
name = "gluing-eppa"
git = "https://github.com/janhubicka/lean-gluing-eppa"
rev = "136bd0f5f47209f090ea4e284a8c6a4c9386d795"
~~~

The tested environment pins Lean `v4.35.0-rc3` and Mathlib
`5bd58ac291422a21f412ae354c91e7d172255a2c`.
Other projects should test their own dependency compatibility.
The library admits smaller imports such as
`GluingEPPA.Sparsening.TreeHomEmbedding`,
`GluingEPPA.Sparsening.OrbitFiniteTower`, or
`GluingEPPA.Sparsening.SparseningTheorem`.

See [Using the library](docs/wiki/Using-the-library.md) for the
precise public theorem inputs, namespaces, and reusable components.

## Proof and validation

The proof uses actual induced closed charts, a complete overlap graph,
supported Boolean valuations, an affine endpoint action, and a genuine
*upstairs* free-cut dichotomy. Finite strict-root tree targets are
assembled by induction on the local-test size. The stage is
`max(1,n)` to guarantee faithfulness even for `n=0`.
An exact rooted tower carries the **same original partial maps**
and their coherent composition identities through the iterations.

The formalization does not invoke the previous sparsening theorem
in `AllThoseEPPA.MainTheorems`. It validates this complete-overlap
construction on its own. `PartialFamily.coherentBase` concerns
inverse-compatible padding, **not** coherent EPPA; for coherent
families use `OrbitAtlas.CoherentFamily`.

Run the kernel and source audits with:

~~~sh
lake update
lake exe cache get
lake build
for manifest in scripts/Check*Axioms.lean; do
  log="\${manifest%.lean}.log"
  lake env lean "$manifest" > "$log"
  python3 scripts/check-axiom-log.py "$log" "$manifest"
done
python3 scripts/check_saturated_cover.py --exhaustive
python3 scripts/check_atlas_action.py
python3 scripts/check_orbit_atlas.py
python3 scripts/audit_library_imports.py
python3 scripts/check_wiki_docs.py
~~~

The Python suites, structural audit and adversarial self-audits are
**not substitutes for kernel checking** or an independent mathematical
referee comparing the Lean definitions with the published statement.
The proof is for a **fixed language**; it does not permit permutations
of relation symbols, and it does not assert *induced* local-tree embeddings.

The written manuscript, complete formal-statement ledger and author edits
belong to [`janhubicka/Otto-simplified`](https://github.com/janhubicka/Otto-simplified).
**Keep manuscript TeX out of this Lean repository.**
