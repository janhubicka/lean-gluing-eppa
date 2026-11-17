# Part II integration, 17 November 2026

## Scope and base

This work concerns recursive gluing valuations in manuscript Part II.
It proves geometric chain restriction, the actual augmented recursive
family and its Links, and bounded coset/component-cycle exclusion.
It does not yet prove augmented naturality or the complete prescribed-overlap
and locally tree-like realization theorem.

The integration starts at main commit
`990a2852ee9eba051f8b1a7e3c1835dd605eb53f` and incorporates the following
previously separate proof branches:

| PR | Integrated head | Subject |
| --- | --- | --- |
| #226 | `c4cfa91af33e73e87bd5439ea9d586e207c00933` | Finite original interface separation |
| #220 | `68884c734072c8049638a2fe72fceadbd012bd4a` | Exact active boundary shifts |
| #227 | `11123416c3c23decb40de427895eb4ad246f2919` | Separation from interface images |
| #221 | `3213b5c117754fd43227b583242eca2410d6656e` | Full-or-proper active interval |
| #222 | `21b3ff6dee11f4dc5375407557afc01d839edaf1` | Bounded active interval length |
| #192 | `87460c4c2ca871b13dcecb79bd7466d96eca4a3f` | Proper-mask reindexing and raw chains |

These are integrated for joint validation; no assertion about their earlier
CI status is inferred from their mergeability or absence of admission tokens.

## Actual normalized interfaces and tests

`HistoricalInterfaceMultiplication` proves the parameter multiplication
laws for every boundary of the original finite covered history. A generic
historical boundary stores parameter functions, so the laws must be proved
for the actual construction; pointwise chart agreement alone does not imply
them.

`ActualActiveNormalizedSeparation` then proves the unique smaller-group
shift equation and canonical normalized coset disjointness for each pair
of consecutive actual active interfaces. The whole normalized interface
commutes with the translated original block charts. Original linkedness,
pointwise correctness and historical interface separation are discharged
by the finite construction.

`NormalizedProperSeparatedChain` identifies the actual smaller-stage
interface subgroup ranges across the reassociation
`(M ∩ A) ∩ (M ∩ B) = M ∩ (A ∩ B)`. A bounded nonempty list with these
normalized separations therefore belongs to the actual `SeparatedChains`
family. `NormalizedBoundaryAssembly` constructs that list from consecutive
boundaries while retaining its shifts and ordered source masks.

`ActualActiveSeparatedTest` specializes the construction to an original
proper active interval. Its `ProperActiveInterval` retains the literal
history decomposition, component reachability and properness. Its chosen
interface parameters and shifts retain their original coordinate equations.
The normalized source list has exactly the original interval's ordered
source masks and length; `.test` is a genuine earlier-stage finite test.

## Actual chain traversal

`ActualChainTraversal` constructs the moved endpoint in the literal finite
chain test. Each block displacement is represented by an allowed word in
its own earlier group. Their concatenation follows genuine edges through
the original `buildNonempty`; the proof transports those paths through
each actual old-side embedding. An initial identity outside the first exit
attachment remains outside every subsequent last block.

`chainPerm_traversal_moves` therefore supplies a moved point of the actual
recorded test, including its completed permutations. The permutation order
is explicitly identified with the opposite product used by the augmented
record. `augmented_chain_traversal_not_one` concludes that this traversal
word is nonidentity in the actual augmented stage. It assumes neither a
moved endpoint nor faithfulness of an independently chosen action.

`CosetCycleChainTest` now instantiates the separated test and initial
exit condition from every bounded coset cycle and identifies the traversal
word's augmented value with the telescoping product. The actual-family
specialization is described below.

## Component charts and the finite induction

The chart invariant must retain the pointwise formula for its last block,
not merely an equality of images. It also retains genuine-edge reflection
and inclusion of the translated normalized entry into the original entry.
The latter inclusion derives normalized attachment separation from the
original separation condition.

A component still meeting the newest block carries this last-coordinate
invariant. A component whose active interval has ended carries a plain
component chart: its normalized last block stays unchanged when an inactive
original block is appended. Conflating these cases would give the plain
chart the wrong last source mask.

Every chart carries an intrinsic `NormalizedChainTrace`, indexed by its
exact source state, with block count at most the original chain length.
`ComponentTraceDichotomy` makes the full/proper split on this same trace.
If a trace block contains all of M, its Cayley image is M-saturated and
therefore equals the entire target component. Otherwise all trace masks
are proper in M.

`NormalizedProperAttachmentEquiv` provides the concrete interface group
equivalence, both attaching squares, and genuine-edge-preserving quotient
equivalence for the literal smaller-stage attachment. `OrderedBuildTrace`
proves that a succession of actual `initial` and `step` operations is
exactly the original `buildNonempty` state on its recorded ordered list.
`NormalizedTraceSeparatedTest.testEquiv` combines these facts to identify
the trace source with the actual bounded earlier test, preserving all
labelled edges, last coordinates, and completed permutations.

The final `LinkChain.chain_restriction` theorem, in
`ChainRestrictionNormalForm.lean`, transports
the canonical-history result back to the literal original `chainState`.
It returns either the actual old M Cayley group or a genuine earlier
`SeparatedChains` test with block count at most the original input's,
equivalent to the whole original M-component with genuine M-edge iff.
`chain_restriction_completed_actions` proves the completed M-letter
actions. This closes the geometric chain-restriction statement.

The independent active-interval construction remains a checked positional
description. The final proof uses the intrinsic source trace and does not
need to identify independently chosen interval shifts with the trace's
choices. A chart from an arbitrary `ChainState` would not suffice.

## The actual augmented family

`LinkUniqueness` proves that a Link between fixed Data endpoints is unique:
both inclusion and deletion are determined by their values on generators,
and replacement is a proposition. This removes dependence on arbitrary
choices of equivalent earlier Link packages.

`AugmentedFamilyData` gives a total test-package function of the earlier
Data, choosing the actual bounded chain package when earlier Links exist.
It then specializes the existing well-founded `parameterizedFamily`.
The fallback empty package merely makes this total definition possible;
`AugmentedFamily.actual_tests_eq` proves unconditionally that every
actual recursive input uses the genuine chain package.

At an earlier stage M, the required action on an M-chain is extracted from
that same stage's literal test-permutation coordinate. `RecordedChainActions`
uses the completed-action restriction theorem to cover each current S-chain
by full M-Cayley graphs and actual recorded smaller M-tests. It transfers
the old M-word kernel across these equivariant covers and constructs the
required M-group action. No action on the current test is assumed.

The strong induction in `AugmentedFamily.family_links` uses only
proper target subsets. Its smaller tests use the same N, the same actual
old Data, and exactly the restricted earlier Links. The old component
actions come independently from the retained component coordinate through
the forgetful map. `AugmentedStep.link` therefore has all its premises
discharged. The resulting family has generator-preserving inclusions,
deletions, retractions, injectivity, exact endpoint repair, and coherent
composition of inclusions and deletions. `family_record_eq` identifies
every stage with its literal augmented record.

This internal coherence between edge subsets is distinct from naturality
under isomorphisms of the underlying diagram. The latter remains open for
the chain-augmented family.

## Bounded cycles and reflection in that same family

`CosetCycle` uses the actual subgroups generated by its masks, cyclic
connectivity, and the manuscript's disjointness of adjacent intersection
cosets. The masks are proved proper from separation. Their displacements
are lifted to the actual earlier groups using the proved inclusion-range
identity. Inclusion squares commute because their generator values agree.
The cycle separation then gives the literal chain separation predicate
and puts the first identity outside its exit attachment.

The resulting test has exactly the cycle's number of blocks, bounded by
the same N. Its traversal moves a point, whereas the ordered product of
cyclic differences telescopes to one without assuming commutativity.
`AugmentedFamily.no_bounded_coset_cycle` applies this contradiction to the
actual recursive family; all current-stage Link premises are discharged.

`AugmentedComponentReflection` extracts the required component-action
equality from the actual record. `AugmentedFamily.coset_component_reflection`
then supplies reflection for every pair of masks in the literal full lift,
including whole-alphabet cases. Word generation and endpoint repair use
the same family and Links. Finally `ComponentCycle.toCosetCycle` transports
the manuscript's actual lift connectivity and separation, giving
`AugmentedFamily.no_bounded_component_cycle` for lengths two through N.
These conclusions do not assume a chosen separated test, a moved endpoint,
faithfulness of an unrelated action, or absence of cycles.

## Compatibility repairs

The inherited recursive call in
`HistoricalBoundaryList.AdjacentInterfacesDisjoint` supplied section
arguments which are not parameters of the recursive call during its own
definition. The corrected call uses only the tail. The final append proof
now makes list associativity explicit. These repairs do not change the
mathematical statement.

`normalized_interface_coset_maps_into` now allows independent universes
for its four group carriers. Its original proof is unchanged. This permits
the genuinely heterogeneous historical-interface specialization.

Broad Mathlib imports in shared foundations are replaced by their specific
dependencies; any consumer needing a previously implicit import receives
that import explicitly. No compiler or mathlib pin is changed.

## Validation and open obligations

Pinned Lean: `leanprover/lean4:v4.35.0-rc3`.
Pinned mathlib: `5bd58ac291422a21f412ae354c91e7d172255a2c`.

The initial consolidated geometric snapshot, published as
`bc3042613273984a677ea082055d5458e1632447` in draft PR #228, passed the
following local checks:

- The exact pinned native Lean compiler checked the complete default
  import closure: **332 modules**, comprising all 331 library modules and
  the public `GluingEPPA` root. Compilation followed topological dependency
  order with the pinned package paths. Every final source SHA256 matched
  its successful compilation record.
- The deduplicated union of **all 79 named axiom manifests** checked
  **1,193 unique declarations**, with exact-name matching and no manifests
  skipped. Only `propext`, `Classical.choice`, and `Quot.sound` occurred.
  Every manifest digest matched its audited version.
- The public import audit covered all 331 library modules. Reducing
  `ChainValuation.All` from 141 direct imports to 20 preserved its exact
  194-module local dependency closure.
- The 184 chain-module source inventory contained no explicit admissions
  or axiom declarations. `git diff --check` passed.

The full default check was a native Lean source/kernel validation, not a
claim that a final default `lake build` invocation completed. Earlier
focused Lake builds did complete, including the 1,132-job Part II and
`FiniteIntersections` build. The 146-module legacy closure also passed
after explicit import repairs.

The ordinary reproduction commands are `lake build`, followed by running
each `scripts/Check*Axioms.lean` with `lake env lean` and checking its log
with `scripts/check-axiom-log.py`; `scripts/audit_library_imports.py` and
`scripts/audit_part_ii_source_use.py` provide the separate structural
inventories. Import closure and lexical inventories are not semantic
proof certificates or completion percentages.

The final augmented-family and cycle integration also passed the complete
combined checks:

| Check | Final result |
| --- | --- |
| Exact pinned native Lean default closure | 340 modules, all successful |
| Current source digests | All 340 match their checked records |
| Public library import coverage | All 339 library modules |
| Complete named axiom audit | 1,251 unique declarations from all 84 manifests |
| Allowed axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound` |
| Current manifest digests | All 84 match the audited union |
| Chain source inventory | 192 modules, zero explicit admissions |
| Final All simplification | 21 direct imports reduced to 16, same 202-module closure |
| Whitespace | `git diff --check` passed |

The final dependency build rechecked the augmented-family action and Link
consumers, the final cycle endpoint, the minimized All and the public root
against their latest artifacts. The method distinction above still applies:
this final whole-library check used native Lean, not a completed final
default Lake invocation.

The versioned `part-ii-integration-20261117-evidence.json` retains all source
and manifest digests, compiler pins and counts. The adjacent
`part-ii-integration-20261117-axioms.log` retains the complete exact-name
axiom output. The manifests themselves remain the reproducible inputs.

The remaining manuscript Part II obligations are naturality under diagram
isomorphisms for this augmented family; the specific finite coherent
prescribed-overlap realization; the carrier-to-hypergraph transfer and
finite join-tree criterion; and the all-copy local sections and set-valued
structure transfer. The simultaneous augmented recursion and the bounded
coset/component-cycle arguments are no longer open obligations.

The next naturality step is concrete: construct, under each diagram
isomorphism and the inductively given earlier group isomorphisms, a
same-length relabeling of every bounded chain and an equivalence of its
`chainSpace` conjugating the letter permutations. Existing pushout
equivalences and matching-completion conjugacy supply local tools, but
this chain-level assembly is not yet proved. It would give the added-test
coordinate of augmented word-equality transport; the existing old-coordinate
argument and `Data.exists_equiv_of_word_equalities` can then be reused.
`RecursiveNaturality` currently refers to the original unaugmented family,
so it cannot simply be cited for this new family.

The manuscript setup now explicitly assumes both earlier requirements
(a) and (b), matching the packaged `Link` interface. Both are available
in the intended simultaneous induction. The main theorem is unchanged.
