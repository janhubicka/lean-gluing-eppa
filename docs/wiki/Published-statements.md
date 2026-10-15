# Published statements and the checked Lean formulation

## Source and conventions

**Working text:** Sofia Brenner and Jan Hubička,
[*A simple proof of EPPA for a lot of things*](https://github.com/janhubicka/Otto-simplified/blob/main/amalgamation_diagrams.tex).
The sparsening statement is Theorem 7.5 of the Hubička–Konečný survey
[*Twenty years of Nešetřil's classification programme of Ramsey
classes*](https://arxiv.org/html/2501.17293v5). The theorem number
depends on the survey version; this table uses the v5 postprint.

The notation \`A ⊆ B0\` denotes a **closed, induced** copy when
unary functions are present, not merely a relation-preserving injection.
All symbols of the language are fixed by automorphisms.

## Main theorem crosswalk

| Mathematical statement | Checked Lean declaration | Meaning and scope |
| --- | --- | --- |
| EPPA for arbitrary finite structures in a fixed finite **relational** language | \`GluingEPPA.finite_relational_eppa_private\` | An induced finite witness for all partial automorphisms; nullary relations and repeated coordinates are included |
| Ordinary sparsening EPPA | \`GluingEPPA.Sparsening.OrbitAtlas.sparsening_eppa\` | From any finite initial EPPA witness for a closed irreducible root, construct a finite faithful EPPA witness with projection and local trees |
| Coherent sparsening EPPA | \`GluingEPPA.Sparsening.OrbitAtlas.coherent_sparsening_eppa\` | If the original choices compose coherently, the **same construction** preserves coherence |
| Simultaneous result record | \`GluingEPPA.Sparsening.OrbitAtlas.SparseningWitness\` | Exact root copy, all extensions, projection, faithfulness, and local trees, all on **one** finite carrier |
| Numerical local-tree induction | \`GluingEPPA.Sparsening.OrbitAtlas.FiniteRooted.tower_localTrees_fixedBase\` | Every closed test of at most \`n\` points at stage \`n\` has a tree image over the original root |
| Actual fixed-root projection | \`GluingEPPA.Sparsening.OrbitAtlas.FiniteRooted.projectToBase_root\` | Composite projection fixes the canonical embedded root |
| Faithfulness in the original language | \`GluingEPPA.Sparsening.OrbitAtlas.FiniteRooted.tower_reduct_faithful\` | At each **positive** refinement stage, all closed irreducible tests can be moved into the distinguished root |
| Actual coherent transport | \`GluingEPPA.Sparsening.OrbitAtlas.FiniteRooted.towerFamily_coherent\` | Retains the original partial-map index set; proves composition for all matching triples |

The central \`SparseningWitness\` has fields that directly spell out the
four clauses of the displayed theorem:

1. \`faithful\`: every closed irreducible substructure of the constructed
   witness can be moved into the actual embedded root by an automorphism.
2. \`projection\`: a homomorphism-embedding from the whole witness
   back to the original initial witness, with \`projection_root\`.
3. \`local_trees\`: every closed test of at most \`n\` vertices has a
   homomorphism-embedding into a **finite strict full-root tree**.
4. Coherence: the coherent theorem additionally supplies
   \`CoherentFamily W.extension\` for the same witness \`W\`.

The strict target is stronger than the general tree-amalgamation target:
each gluing interface lies inside an actual full copy of \`A\` on **both**
sides. For an irreducible base, these strict trees are tree amalgams in
the survey's stated sense.

## Hypotheses that must not be suppressed

- \`A\` is finite, **irreducible** and **closed** in \`B0\`; \`B0\`
  is finite and already has the input EPPA extension property.
- All relations are arity-indexed; unary functions are set-valued
  and may be cyclic, branching or have empty fibres.
- A homomorphism preserves complete unary fibres **as sets**.
  A homomorphism-embedding is exact on closed irreducible tests,
  not globally injective.
- Local test size \`n = 0\` is allowed. The actual construction
  performs \`max(1,n)\` refinements so faithfulness still holds.
- The coherent variant assumes composition-respecting *input choices*.
  It does not infer coherence from ordinary EPPA.

## Differences from the prose proof

The manuscript gives a compact sketch of the entire iteration and its
coherence. Lean makes several boundary statements explicit:
\`ClosedPartialAut.IsComposition\` identifies the actual composition,
\`rootEmbedding_surjective\` fixes what is genuinely surjective,
\`refinedRootExact\` records whole unary fibres, and
\`FullATree.changeBase\` transports the actual tree-pushout maps
instead of using an unproved equivalence of tree targets.

This is a **new proof via complete-overlap Boolean gluing**, not an import
of the older sparsening argument in the All Those EPPA classes library.

## Not asserted

- Permutations of the language symbols by the partial automorphisms.
- The existence of a globally injective projection or globally induced
  embeddings of local tests into trees.
- Coherent extension choices obtained from ordinary EPPA alone.
- An independent referee's endorsement of the text-to-Lean
  statement correspondence.

The whole-theorem declarations passed full build and
[331 named axiom checks](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38738905840)
and a [separate merged-main build](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38739744079).
