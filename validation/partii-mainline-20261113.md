# Part II mainline validation — 13 November 2026

## Checked integration

PR #163 was merged with history retained as
`2a73cbf1e7d7f21ff1193cbb37a3079d27415494`.
The incorporated proof head `3b9b5ac52b354d789844ec1f06b6cd50552f8889`
passed the full Lean build, every named axiom manifest, finite regressions
and structural checks in run 43384605490. The source-use inventory passed
in 43384605476. This document does not change the checked proof tree.

The integrated results include finite historical source-pair order,
original-builder correspondence, injective historical embeddings and
parameters, exact overlaps and interface equivalences, equivariant test-cover
kernel transfer, and the resulting right-action/generator/word compatibility.

This is not a kernel certificate for the global chain-restriction theorem,
the existence of every required chain-test cover, the simultaneous augmented
recursive family, or N-acyclicity. Those manuscript obligations remain pending.

## Closed obsolete stack entries

The read-only Git ancestry inventory verified all the following exact PR
heads as ancestors of the checked integration. They were closed after the
merge, retaining every branch and commit:

162, 160, 158, 157, 156, 155, 154, 151, 150, 149, 148, 147,
120, 119, 102, 100, 94, 90, 89, 87, 85.

There are 21 entries. Their returned closure head SHAs match the inventory.
The old failing intermediate builds do not override the successful later
repairs present on main. Closing the PR shells does not discard their work.

PR #161 was also closed as content-superseded, on a different basis:
`EquivariantTestCovers.lean` at its checked head
`0f36d38bd87338a05ecdab5c0dced327123a4120` and on main has the identical
blob `71e3375ec596b864180d49f3c3a9fe3d3a1edb67`. Both declarations are
included in the checked `CheckCoverRightActionAxioms.lean` manifest and
consumed by `CoverRightAction`. Its separate historical branch and note
remain available. This is exact content inclusion, not Git ancestry.
Thus 22 obsolete Lean PRs have been closed, in addition to merging #163.

Distinct nonancestor branches remain open. In particular, failed normalization
candidates are not merged just because GitHub can combine their text.
A separate consolidation check on `partii-postmerge-validation-20261113`
attempts only pinned heads with successful full Lean runs; it resolves only
import/axiom-list unions and refuses conflicting proof-file resolution.
That combined check is pending, not evidence that those extra branches are
already on main.

## Dead-code cleanup

The integrated revision already removes a consecutive duplicate `change`
in `WordAction.lean`. On the postmerge validation branch, the compiler-reported
unreachable trailing `tauto` in `LinkRestrictedMatching.lean` has been removed;
the inspected patch changes exactly that one tactic line. The obsolete
parallel macOS workflow has also been removed on that branch. Both changes
await the combined validation and are not represented as merged here.

Import reachability and lexical non-use do not justify deleting generic
proof modules. No live normalization ingredient was deleted on that basis.

## Continuing formalization

Draft PR #164 adds `HistoricalInternalPaths.lean` and a three-declaration
axiom manifest. It connects the historical coset charts to the actual earlier
Link Cayley theorem, yielding:

1. ambient M-connectivity between chart points iff an M-path inside the
   original historical block;
2. an internal path between two representatives reached from one ambient root;
3. a unique displacement in the genuine earlier K_(M ∩ A), satisfying the
   left-translation equation x * incl(u) = y.

The historical chart is an explicit input. Aligning the charts with every
actual consecutive boundary and assembling the global normalized component
remain necessary. PR #164 is source-level work pending its fresh Lean run;
no green manuscript marker is assigned to it.
