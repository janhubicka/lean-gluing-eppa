# Gluing EPPA — Lean library

A formalization of finite relational EPPA using gluing diagrams, followed by
the complete-overlap sparsening construction for relations and set-valued
unary functions. **No manuscript TeX is stored here.** The written proof and
its declaration-level validation ledger live in
[`janhubicka/Otto-simplified`](https://github.com/janhubicka/Otto-simplified).

## Current checked scope

**The complete ordinary and coherent sparsening EPPA theorems are formalized.**
The merged head is [`136bd0f5f47209f090ea4e284a8c6a4c9386d795`](https://github.com/janhubicka/lean-gluing-eppa/commit/136bd0f5f47209f090ea4e284a8c6a4c9386d795),
via [PR #56](https://github.com/janhubicka/lean-gluing-eppa/pull/56).
The [final PR build](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38738905840)
and [merged-main build](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38739744079)
passed. The audit records **331 declarations matched by name** across four
manifests (281 + 21 + 12 + 17), allowing only `propext`,
`Classical.choice`, and `Quot.sound`. All three finite regression suites
passed; these are supplementary checks, not mathematical proofs.

The exported ordinary theorem is
`GluingEPPA.Sparsening.OrbitAtlas.sparsening_eppa` and the coherent theorem is
`GluingEPPA.Sparsening.OrbitAtlas.coherent_sparsening_eppa`.
Both live in `GluingEPPA/Sparsening/SparseningTheorem.lean` and depend on
the *new canonical complete-overlap construction*, not a previously proved
sparsening result from another library. In the finite target, both the
projection and the exact root copy refer to the **same witness**. The result
covers arbitrary fixed relation symbols and whole set-valued unary functions.
There is no claim about permutations of language symbols.

The complete source and human-readable proof are in
[`janhubicka/Otto-simplified`](https://github.com/janhubicka/Otto-simplified).
For an audit of exact hypotheses and the one-generated-closure bridge, see
the manuscript's [validation ledger](https://github.com/janhubicka/Otto-simplified/blob/main/VALIDATION.md).

## Unconditional finite relational EPPA

`GluingEPPA.finite_relational_eppa_private` constructs a finite induced witness
extending every partial automorphism of a finite relational structure. It
assumes neither a witness nor supplied inverse-compatible total extensions.
Nullary relations, repeated coordinates and empty partial automorphisms are
included. The construction uses Boolean coordinates on unordered base edges
and private transposition/three-cycle markers. The bound `|A| + 2|I|` for the
padded permutation carrier is checked; pruning to the sharper marker count
`2s+3t` is not separately formalized.

`PartialFamily.coherentBase` denotes inverse-compatible choices only, **not**
the composition condition of coherent EPPA.

## Structures and maps

Below, sparsening declarations are relative to the namespace
`GluingEPPA.Sparsening`; `RelStructure` is in `GluingEPPA`.

`RelStructure L A` interprets relation symbols by arity. Unary functions are
maps `F -> A -> Set A`, so outputs may be empty, branching or cyclic.
`UnaryClosed` expresses closure under every output. `inducedRelations` and
`inducedUnary` form the induced structure on a subtype; `inducedUnary_full`
retains whole ambient fibres on a closed subtype.

`Tree.ExactUnaryEmbedding` stores an injective map, relation reflection and
preservation, and equality of complete unary fibres. `IsIrreducible` means
no free decomposition into two proper closed sides.
`Tree.UnaryHomEmbedding` is exact on every closed irreducible test and need
not be globally injective. These maps compose, and their closed irreducible
images remain closed and irreducible.

### Why the internal homomorphism record preserves whole fibres

The module `UnaryGeneratedClosure` defines the least closed set containing
one vertex. `unaryClosure_irreducible` proves its induced structure
irreducible: a closed side containing the generator already contains its
entire closure. Therefore `Tree.UnaryHomEmbedding.out_eq` derives full fibre
equality from exactness on these tests. `image_closed` then proves that
images of all closed sets are closed. None of these lemmas requires
finiteness. Forward unary membership alone would not suffice.

## The canonical refinement

`OrbitAtlas.Chart` indexes actual closed subsets contained in an automorphic
image of the distinguished root, including the empty chart. Charts are not
embedding presentations. `OrbitAtlas.Vertex`, `OrbitAtlas.relations` and
`OrbitAtlas.outputs` build the quotient of valid occurrences `(s,chi,x)` with
`x` in chart `s`. The graph of chart overlaps is complete, and every overlap
is used.

The module `CompleteRecords` identifies quotient vertices by pointed parity
charge and exterior coordinates. The modules `AtlasSeparator` and
`OrbitRootedDichotomy` turn an arbitrary nonempty closed test into a one-chart
test or an actual proper upstairs free cut. The projected overlap is a
closed complete-J root. No freeness is inferred for the old projected image.

`OrbitAtlas.lift` gives actual affine automorphisms. The module
`OrbitEndpoint` checks root-spoke extensions, their pointwise composition
equations, and movement of whole charts into the distinguished root.
`OrbitIrreducible` and `OrbitProjectionHomEmbedding` connect these facts to
irreducible containment, one-step faithfulness and projection exactness.

## Strict full-A trees and local bounds

`Tree.FullATree` has full-copy leaves and free-amalgam gluing interfaces
contained in full base copies on both sides. Its carrier is finite when the
base is finite. A complete-J root lies in a full base copy. The projected-root
gluing lemmas use the actual upstairs free cut, not an assumed downstairs cut.

`OrbitAtlas.localTreeOfBoundedOldTrees`, in `OrbitLocalTreeBounded.lean`,
raises the local size bound from k to k+1. A one-chart test embeds into the
root. Otherwise each proper side, and therefore its projected image, has at
most k vertices; glue the old target trees along the exact projected root.

`Tree.FullATree.changeBase_iff` and `OrbitAtlas.HasTreeImage.changeBase_iff`
show that isomorphic bases define the same target class. Both actual gluing
maps remain unchanged by inserting the base isomorphism and its inverse.
`OrbitAtlas.localTreeOfBoundedOldTrees_nextRoot` returns the bound based on
the new distinguished root, ready for iteration.

## The actual finite tower

`OrbitAtlas.FiniteRooted` packages a finite expanded structure and a closed
complete-J root. It does **not** assume EPPA or a local-tree property.
Its `refine` uses the actual canonical quotient and zero-valuation root.
Its recursively defined `tower` is the sequence of these refinements.

The principal exported declarations in `OrbitAtlas.FiniteRooted` are:

- `tower_localTrees`: every closed test of size at most n in stage n has a
  strict tree image based on that stage's actual root;
- `rootEmbedding` and `rootEmbedding_surjective`: exact identification with
  the original root;
- `tower_localTrees_fixedBase` and `tower_local_finite_target`: the same local
  conclusion with the original root fixed and a finite target tree;
- `projectToBase`, `projectToBase_fibres`, and `projectToBase_root`: the actual
  composite homomorphism-embedding, full fibres, and its root-fixing equation.

The empty base case preserves nullary predicates. `FiniteRooted.finite` is
essential when interpreting `Nat.card`: no infinite subtype is silently
treated as an empty finite test. Global injectivity and surjectivity of the
projection are never assumed. Root surjectivity concerns only the exact
root-identification map.

## Full sparsening theorem — reusable interface

`ClosedPartialAut R out` represents an isomorphism between two **closed
induced** structures, with a surjective exact map onto its declared range.
Its `IsComposition` relation is the actual matched-domain composition; the
empty partial automorphism is admitted. `ExtendsAlong` expresses pointwise
extension along the distinguished copy, while `CoherentFamily` quantifies
over all composable triples, not just inverse pairs.

`SparseningWitness R0 out0 root n` contains:

- a finite carrier with relations and whole set-valued unary fibres;
- one exact embedding of the original closed root;
- one family extending *every* original partial automorphism;
- a homomorphism-embedding to `R0` fixing the distinguished root;
- movement of every closed irreducible test into that root by an automorphism;
- for each closed test of at most `n` vertices, a homomorphism-embedding
  into a **finite strict** tree of copies of the original root.

The ordinary existence theorem takes a finite ambient witness and the
extension-existence hypothesis; the coherent theorem takes an actual
coherent initial extension family. The root is assumed irreducible in the
public theorem (and closed in the initial ambient structure). No other
geometry is postulated as an input.

`ClosedPartialAut.withCompleteJ`, `ClosedPartialAut.forgetJ`,
`OrbitAtlas.initialRooted`, `FiniteRooted.towerFamily`, and
`OrbitAtlas.sparseningFromExtensions` identify the exact proof pipeline.
The construction uses stage `max(1,n)` because geometric faithfulness
requires at least one refinement even when `n=0`.

## Verification and supplementary tests

Use the pinned toolchain `leanprover/lean4:v4.35.0-rc3` and Mathlib revision
`5bd58ac291422a21f412ae354c91e7d172255a2c` from `lakefile.toml`:

```sh
lake update
lake exe cache get
lake build
for manifest in scripts/Check*Axioms.lean; do
  log="${manifest%.lean}.log"
  lake env lean "$manifest" > "$log"
  python3 scripts/check-axiom-log.py "$log" "$manifest"
done
```

CI also runs `check_saturated_cover.py`, `check_atlas_action.py`, and
`check_orbit_atlas.py`. These supplementary finite computations include
negative controls; they do not replace Lean proofs or independent referees.
Audit artifacts record the checked commit, logs, pinned dependencies, and
checksums. PRs restore the shared main Lake cache without uploading a
separate multi-gigabyte cache. Only successful main checks may seed it.

## Scope and review

The complete fixed-language statement corresponding to Theorem 7.5 of the
[2025 postprint of *Twenty years of Nešetřil’s classification programme*](https://arxiv.org/html/2501.17293v5)
is now checked. `FullATree` is a stricter target than general tree
amalgamation: its interfaces lie inside actual full base copies. For an
irreducible original root, this implies the survey's required tree class.
The local map is a homomorphism-embedding, not an induced embedding into a
tree; persistent induced squares preclude that stronger claim for this
specific Boolean iteration.

Independent mathematical refereeing is still outstanding. The finite
regression suites, self-audits and Lean kernel checking serve different
purposes and are not interchangeable. Future work can refactor this
library's API without needing to preserve obsolete compatibility wrappers,
but should keep the public theorem types stable or provide migration notes.

After the reduct checks, package the chosen extensions for every original
partial automorphism and transport their domains and ranges along the exact
root maps. Use the two-spoke endpoint identity to prove extension for every
index, and its cancellation identity to preserve coherence for every
composable pair. Then combine this with the checked geometric tower into
the exact sparsening EPPA conclusion.

The local conclusion is a homomorphism-embedding into a tree, not an induced
embedding: repeated Boolean refinements can retain an induced square.
Independent mathematical refereeing remains outstanding; the recorded
adversarial passes are self-audits, not independent-agent reports.
