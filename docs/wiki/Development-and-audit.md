# Architecture, build and cleanup discipline

The code is a research library. It should expose theorems and reusable
lemmas to downstream mathematicians, not preserve every historical
internal wrapper as a permanent public API.

## Source layout

The top-level `GluingEPPA.lean` reexports the entire library.
Its two major bodies are:

- **Unconditional finite relational EPPA:** `Basic`, `Relational`,
  `PermutationDiagram`, `PartialFamily`, the oriented/unordered
  cover modules, private-cycle padding and the three ordinary
  endpoint modules.
- **Sparsening from an existing witness:** `Sparsening` modules
  covering supported records, the canonical orbit atlas, affine
  symmetries, free-separator geometry, exact unary and
  homomorphism-embeddings, strict full-root trees, the finite tower,
  original-language reduct, coherent extension families and the
  final simultaneous theorem.

The modules are separate so that an application can import
`GluingEPPA.Sparsening.TreeHomEmbedding` without loading every
EPPA-specific definition, or use the unconditional finite
relational theorem without the sparsening abstraction.

## Checked versions and trust boundary

Current complete-theorem baseline:
[`136bd0f5`](https://github.com/janhubicka/lean-gluing-eppa/commit/136bd0f5f47209f090ea4e284a8c6a4c9386d795).
It passed:

1. `lake build`, with pinned Lean `v4.35.0-rc3` and Mathlib
   `5bd58ac291422a21f412ae354c91e7d172255a2c`;
2. `scripts/CheckAxioms.lean`: 281 named declarations;
3. `scripts/CheckFamilyAxioms.lean`: 21 declarations;
4. `scripts/CheckReductAxioms.lean`: 12 declarations;
5. `scripts/CheckSparseningAxioms.lean`: 17 declarations;
6. three finite regressions, including adversarial negative controls.

The axiom checker rejects missing, duplicated or misidentified named
declarations as well as any dependency outside
`propext`, `Classical.choice` and `Quot.sound`.
This is not a proof that the chosen Lean definitions are faithful
to the survey; that requires a separate statement audit.

## Simplifying and cleaning without losing coverage

There are several distinct concepts of "dead code":

- An **unused direct import** in the umbrella entrypoint is a harmless
  redundancy if another imported module reaches it transitively.
  The import-DAG script computes this conservatively.
- A **legacy theorem wrapper** with no downstream references may
  be removed after checking any known clients, its presence in
  the axiom manifest, and documentation links.
- A **mathematical alternative construction** may be important even
  if the final proof takes another route. Keep the oriented,
  unordered and private-marker EPPA endpoints for independent users.
- A **source file not imported at all** is a different concern
  from a file not mentioned in a paper. The CI import scan
  identifies the former.
- A **commented counterexample / negative control** is not a
  proof dependency but should be kept when it guards a known false
  stronger statement.

Do not prune proof declarations just by grepping for a name:
Lean elaboration, namespaces, tactics, and typeclass inference can
introduce dependencies not visible to a lexical search.

Use `scripts/audit_library_imports.py` for the import closure and
recommended smaller umbrella, then require the whole pinned Lean
build and all named axiom checks on the proposed cleaned branch.
The CI script is an **additional structural guard**, never a
replacement for theorem verification.

## Dependency discipline

Sparsening is compiled from its own quotient records and tree
amalgamation lemmas, **without** invoking the already-proved
sparsening theorem in the external All Those EPPA classes library.
The survey library can be consulted to compare definitions;
its different Lean/Mathlib pin prevents silently treating
similarly named types as definitionally identical.

No category-theoretic interface is required. The exported
objects are explicit functions, finite types, induced structures,
subsets, permutations, whole unary fibres, exact embeddings,
homomorphism-embeddings and full-root tree amalgams.

## CI and local validation

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
~~~

Run `python3 scripts/check_wiki_docs.py` for relative documentation
links. All audit scripts are supplemental to the kernel checks.
The GitHub Actions artifact records the source SHA, pinned
dependencies, logs and checksums. PRs reuse a cache from the
default branch; they do not upload a separate multi-gigabyte
cache. All proof changes must pass CI before merging.

The [publishing page](Publishing.md) explains why
source-controlled wiki Markdown and the GitHub Wiki tab
must be verified separately.
