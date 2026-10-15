# Adversarial referee and maintenance audit

**Status:** The main ordinary/coherent sparsening theorems are Lean
kernel-checked at
[`136bd0f5`](https://github.com/janhubicka/lean-gluing-eppa/commit/136bd0f5f47209f090ea4e284a8c6a4c9386d795).
The PR build and merged-main build passed, with 331 **named**
axiom targets and only the standard `propext`, `Classical.choice`,
and `Quot.sound` axioms. The finite regression suites are separate,
supplementary tests.

The passes below are intentionally adversarial **self-audits**.
They are not the report of three independently appointed
human or AI referees. Independent mathematical comparison of the
Lean definitions with the manuscript remains welcome.

## Pass I: statement fidelity

| Potential mismatch | Test or resolution |
| --- | --- |
| Local map accidentally required to be globally injective | Final witness uses `UnaryHomEmbedding`, exact only on closed irreducible tests |
| Coherent EPPA confused with inverse-compatible extensions | Coherent family quantifies over **every composable triple** with matching middle range/domain |
| Partial isomorphisms omitted, or empty maps excluded | `ClosedPartialAut` ranges over all closed induced substructures; empty domain is included |
| Root not actually induced/closed | `rootEmbedding` is `ExactUnaryEmbedding`; full unary-fibre equality forces closed range |
| Faithfulness claimed at stage 0 | Final construction uses `max(1,n)`; the statement handles `n=0` |
| Unary functions silently replaced by forward relations | `out_eq` proves equality of the entire set-valued fibre from one-generated irreducible tests |
| Arbitrary language-symbol permutations claimed | Explicitly **excluded**; only fixed languages are formalized |
| Strict tree versus general tree amalgam | Strict full-root tree is stronger when the base is irreducible |
| Unsound conversion of local trees to induced embeddings | Rejected; the theorem deliberately asserts homomorphism-embeddings |

The full structure `SparseningWitness` packages all conclusions
on the same finite carrier, ruling out accidentally selecting
unrelated witnesses for the individual clauses.

## Pass II: construction and counterexample attacks

**False inference 1: projected old pieces are free.**
An upstairs free decomposition cannot in general be pushed down
along a homomorphism-embedding, even one that happens to be injective.
For a toy model, the edge-preserving inclusion of an induced path
`P4` into the cycle `C4` preserves path edges but the additional
old endpoint edge destroys the cut. The proved gluing lemma instead
uses **the actual upstairs free cut**, with the old projected overlap
serving only as the attaching root.

**False inference 2: chart indices can be chosen presentations.**
Different embedding presentations of the same closed subset can
interfere with the affine action and the overlap graph. The canonical
orbit atlas uses **actual subsets**, and the action on them is literal
set image.

**False inference 3: all chart occurrences exist.**
The quotient only includes triples with `x∈s`.
The supported-walk/record equivalence never introduces vertices
outside their support.

**False inference 4: adding J is harmless at every stage.**
Only the first stage makes `J` complete on the entire initial
witness. Completing `J` at every stage would invalidate the
separators and the size induction.

**False inference 5: inverse compatibility proves coherence.**
A family of total extensions can respect all inverses while failing
composition on a composable noninverse pair. Coherence is proved by
the explicit two-spoke cancellation, not inferred from the private
marker padding used for ordinary relational EPPA.

**False inference 6: all roots need only embed in the previous root.**
A root chart must be exactly isomorphic *onto* the new distinguished
root so that finite tree bases can be compared without changing
their full building blocks. The proof includes explicit surjectivity
on this restricted map. It never claims surjectivity for the
whole quotient projection.

**False inference 7: local trees could be induced.**
A persistent valuation square in the complete-overlap construction
can retain an induced four-cycle at every positive stage. Therefore
the local-map claim cannot be strengthened to a global induced
embedding for these witnesses.

## Pass III: formal trust and software maintainability

The main `GluingEPPA.lean` umbrella imports every library module.
A syntactic dependency-graph audit can identify redundant direct
imports, but *deleting proof modules from the filesystem* solely on
that basis is unsafe: a module can be useful to external clients
even if it is not reached by another theorem.

The reproducible structural script
[`scripts/audit_library_imports.py`](../../scripts/audit_library_imports.py)
reports local module count, the acyclic import graph and a proposed
minimal umbrella. It is **not** a proof of mathematical equivalence.
Any import simplification must also pass the complete Lean build,
all 331 named axiom checks and all finite regression suites.

The source contains some historical/alternative ordinary EPPA
constructions (`FiniteEPPA`, `UnorderedFiniteEPPA`,
`PrivateFiniteEPPA`). They are different meaningful checked
APIs; they should not be deleted merely because the last is the
preferred route. Likewise, keep
`PartialFamily.coherentBase` for the inverse-compatible base
family, but do **not** advertise it as coherent EPPA.

The trust boundary is visible. The CI script
`check-axiom-log.py` compares **full declaration names in order**,
not just the number of axiom prints, and refuses unexpected axioms.
The checked source and compiler/Mathlib pins are recorded with
proof-audit artifacts. A separate main-branch check runs after
merging each proof PR. These are reproducibility safeguards,
not substitute referee opinions.

### Remaining obligations

- Genuine independent mathematical referee pass comparing each
  public theorem with the source formulation, not just its name.
- Document any future API renames for downstream users.
- Verify GitHub Wiki publication separately from committing
  the source pages; the wiki is a **different Git repository**.

No mathematical gap is currently asserted in the validated
fixed-language proof. No claim about variants with symbol
permutations or induced local-tree embeddings is made.
