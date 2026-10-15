# Gluing EPPA — a verified Lean research library

This wiki is a mathematician-facing guide to a Lean 4 formalization of
finite relational EPPA by gluing diagrams and the **complete-overlap
sparsening construction** for structures with relations and set-valued
unary functions.

It is intended to be reusable, not tied to a single application of EPPA.
The source manuscript is **A simple proof of EPPA for a lot of things**
by Sofia Brenner and Jan Hubička. The mathematical statement corresponding
to the sparsening theorem appears in the Hubička–Konečný survey,
*Twenty years of Nešetřil's classification programme of Ramsey classes*,
Theorem 7.5 in [postprint v5](https://arxiv.org/html/2501.17293v5).

## Navigate the development

| Page | Contents |
| --- | --- |
| [Using the library](Using-the-library.md) | Lake setup, stable public theorem names, exact hypotheses, sample \`#check\` commands, and narrow imports |
| [Published statements](Published-statements.md) | Precise correspondence of the paper's two main statements with the checked Lean conclusions; explicit scope limitations |
| [Proof architecture](Proof-architecture.md) | A short human-readable proof from gluing EPPA through complete-overlap refinement and the finite tower |
| [Finite relational EPPA](Finite-relational-EPPA.md) | Original gluing diagrams, permutation extensions, unordered edges, and private markers |
| [Sparsening construction](Sparsening-construction.md) | Canonical charts, quotient, affine automorphisms, free cuts, rooted tree gluing, faithfulness and coherence |
| [Auxiliary lemma index](Auxiliary-lemmas.md) | Reusable definitions and lemmas, file by file, including exact unary fibres and change of base |
| [Adversarial referee audit](Adversarial-referee-record.md) | Three separate self-audits: mathematical fidelity, kernel trust, and maintenance/dead-code candidates |
| [Development and audit](Development-and-audit.md) | Dependency structure, reproducibility, test scope, proof status and design decisions |
| [Wiki publishing](Publishing.md) | Automatic synchronization to the GitHub Wiki tab and one-time initialization instructions |

The maintained source is [\`docs/wiki/\`](https://github.com/janhubicka/lean-gluing-eppa/tree/main/docs/wiki);
the separate [GitHub Wiki](https://github.com/janhubicka/lean-gluing-eppa/wiki)
is synchronized by Actions **once its first Home page has been initialized**.
Until then, the source-controlled pages are fully readable.

## Main theorem endpoints

~~~lean
import GluingEPPA

-- Unconditional finite relational EPPA (the private-marker construction).
#check GluingEPPA.finite_relational_eppa_private

-- Finite complete-overlap sparsening of an initial EPPA witness.
#check GluingEPPA.Sparsening.OrbitAtlas.sparsening_eppa

-- Preservation of coherent EPPA for the same sparsening witness.
#check GluingEPPA.Sparsening.OrbitAtlas.coherent_sparsening_eppa

-- The exact simultaneous conclusion record.
#check GluingEPPA.Sparsening.OrbitAtlas.SparseningWitness

-- Reusable locally exact homomorphism-embeddings and strict full-A trees.
#check GluingEPPA.Sparsening.Tree.UnaryHomEmbedding
#check GluingEPPA.Sparsening.Tree.FullATree

-- A complete-fibre equality derived from local exactness.
#check GluingEPPA.Sparsening.Tree.UnaryHomEmbedding.out_eq
~~~

The complete ordinary and coherent sparsening theorem was checked in
[merged commit \`136bd0f5\`](https://github.com/janhubicka/lean-gluing-eppa/commit/136bd0f5f47209f090ea4e284a8c6a4c9386d795):
the full Lean build, **331 named axiom-audit targets** and all three
finite regression suites passed. The statement covers a **fixed language**,
with arbitrary relational symbols and whole set-valued unary functions.
It does **not** assert induced local-tree embeddings or permit permutations
of the language symbols.

Formal validation establishes the Lean propositions. It does not by itself
replace the separate mathematical task of matching their definitions to
the printed theorem; the [statement crosswalk](Published-statements.md)
and [adversarial audit](Adversarial-referee-record.md) make that explicit.
Genuine independent mathematical refereeing is not claimed.
