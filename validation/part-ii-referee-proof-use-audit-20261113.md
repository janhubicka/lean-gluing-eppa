# Part II referee and proof-use audit — 13 November 2026

Scope: the recursive valuation draft, especially `lem:chain-restriction`,
`lem:chain-exact-properties`, and `thm:chain-valuation`. This is not the
separate girth Ramsey project. Verified Part I is unchanged.

## Confirmed compiler evidence

These statuses were read from completed GitHub Actions jobs, not inferred
from source appearance or an open PR description:

| Exact commit | Run | Evidence | Scope |
| --- | --- | --- | --- |
| `c8c0da3527a958d85bdb44cf04ab9e2d4ce0f9ae` (#160) | `43283711227` | Full build, named axiom audits, finite regressions and structural audit succeeded | Finite historical boundaries, source-mask order, injectivity, original-builder correspondence, exact overlap and embedded interfaces |
| `0f36d38bd87338a05ecdab5c0dced327123a4120` (#161) | `43285164917` | Independent cover module build and named axiom audit succeeded | Generator-equivariant maps transfer word equalities through jointly surjective covers |
| `e8cc81755de7debd8a798f295c5716bdff83adfc` (#162) | `43286104481` | Full build and all audit steps succeeded | Actual interface equivalences, both commuting squares, and interface points in components meeting both historical sides |

These runs do not prove the all-length normalized component theorem, the
existence of all required covers, the complete augmented recursive family,
or the final N-acyclicity theorem. The manuscript's whole-theorem markers
must stay pending. Links to these results are partial-support markers.

## What the existing structural audit does, and does not, check

`scripts/audit_library_imports.py` reads the import DAG, checks that every
library module is reachable from the umbrella, rejects duplicate/redundant
root imports, and checks for missing imports/cycles. This is a useful build
coverage check. But importing a theorem, or printing its axioms, does not
make it a dependency of any mathematical conclusion.

In particular, `ChainRestrictionCore.lean` contains local subgroup/coset
calculations; its name does not establish the manuscript's global chain
restriction. `AugmentedLinks.lean` takes the required earlier test actions
and generator compatibility as hypotheses. `CycleUnwindingCore.lean`
proves the final contradiction conditional on an actual moved endpoint.
`ComponentReflection.lean` has explicit action/record/repair hypotheses.
Those assumptions must be instantiated by the actual recursive construction.

No count of imported modules or separately checked lemmas is therefore a
percentage completion of Part II.

## Concrete cleanup

Removed the consecutive duplicate

    change wordActionValue A τ x (A.edge e) = τ e x

in `wordRightAction_edge`. It was a literal repeated no-op, not an
independently useful mathematical lemma. No theorem or hypothesis changed.

No other module is deleted merely for lacking a visible downstream use.
Some are generic interfaces, some are alternative approaches, and others
may be used by typeclass resolution or tactics. Deleting them requires a
consumer audit and a build, not a filename-based judgement.

## New conservative inventory

`scripts/audit_part_ii_source_use.py` explicitly distinguishes:

1. import closure from named construction/interface roots, excluding
   `All.lean` and axiom manifests as mathematical roots;
2. lexical declarations with no other production occurrence, reported only
   as manual-review candidates, not as proved dead code;
3. explicit admission tokens and consecutive duplicate goal changes;
4. the named outstanding manuscript obligations.

It erases nested comments and strings before scanning. It does not claim
fully qualified elaborated dependency analysis; field notation, instances,
automation and theorem aliases can invalidate a lexical unused inference.
The new inventory has not been executed at the time of this note.

## Continue validation by connecting an actual consumer

`CoverRightAction.lean` uses the checked equivariant-cover transfer to
construct the right action required by the augmented inclusion interface:

- `coveredTest_kernel` transfers each relation in the earlier group;
- `rightActionOfEquivariantCover` constructs the group action;
- `rightActionOfEquivariantCover_edge` identifies its generators with the
  prescribed completed letter permutations;
- `rightActionOfEquivariantCover_word` identifies all allowed word actions.

All cover and source-kernel hypotheses remain explicit. This is a genuine
consumer of the cover theorem, rather than a new umbrella import alone.
It still does not supply the geometric covers of the actual finite chain
tests. A separate manifest `CheckCoverRightActionAxioms.lean` includes these
four declarations and their two cover prerequisites.

The new consumer module and cleanup are source candidates until the new
exact-head build succeeds. The historical successful runs above are not
reused as certificates for these changes.

## Referee recommendations and proof status

The manuscript edits centralize structure transfer for set-valued functions,
retain arbitrary small-set sections only on the relational reduct, replace
ambiguous amalgamation segments by exclusive runs of triples, prove
transitivity on parametrized copies, and make both lifted-copy hypotheses
explicit. The unused converse of the local-section lemma is removed from
the English argument; there is no claim that a corresponding Lean module
has been found and removed.

The report's finite-model claims and blanket mathematical verdict are not
new Lean evidence. The direct English proof of global chain normalization
has been clarified, but its global chart/action assembly remains pending.
The distinction between component cycles and coset cycles is retained
because it separates the combinatorial realization argument from the
recursive valuation group argument.
