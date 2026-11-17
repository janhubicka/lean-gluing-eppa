# Matched-step last-coordinate invariant, 17 November 2026

## Scope

`GluingEPPA/Steiner/ChainValuation/MatchedComponentLastChart.lean` supplies
one concrete normalization step for the manuscript's actual
`LinkChain.step`. It does not claim the finite-list chain-restriction
theorem, the existence of all earlier chain test actions, or higher
acyclicity.

The new `ComponentLastChart` invariant retains an exact equivalence from
a normalized `ChainState` onto the whole original `M`-component, genuine
edge preservation and reflection for every letter in `M`, and the
pointwise identity on its last block

```
(equiv (source.lastEmbed t)).val = original.lastEmbed (base * incl t).
```

This last identity, rather than equality of the two chart images, is what
makes the next attaching square commute in the noncommutative groups.
The invariant also records that translated normalized entry coordinates
lie in the original entry set. This inclusion is sufficient; no equality
of the two entry sets is assumed.
It now includes `NormalizedChainTrace`, indexed by the exact source state,
which certifies its concrete succession of one-block initialization and
separated normalized attachments.

## Concrete extension

The extension uses the literal normalized triple-mask maps, a chosen
interface parameter `k`, and a shift satisfying

```
base * incl shift = originalShift * left k.
```

The whole original attaching fibre is derived from
`step_oldComponent_attachment_fibre_iff` and the already checked
`matchedLinkCoset_interface_equiv`. It is not a new assumption. The
normalized left attaching map is `lastEmbed (shift * normalizedLeft t)`;
the right map is `normalizedRight t`.

`ComponentLastChart.initial` constructs the invariant in a literal single
original Cayley block using the earlier restricted coset equivalence.
`ComponentLastChart.extendEquiv` specializes
`stepComponentChart_equivActual` to these concrete maps. Its two value
theorems give the original old-side embedding and the new translated
last-block embedding. `extendEquiv_edge_iff` specializes the genuine-edge
theorem. Original separation and the retained entry-coordinate inclusion
imply separation in the normalized chain state through
`ComponentLastChart.normalized_attachment_disjoint`.
`ComponentLastChart.extend` returns the full invariant on the literal
normalized chain extension, including the next entry-coordinate inclusion.
`ComponentLastChart.perm_val` obtains the
completed letter action from genuine-edge reflection, including the
fixed points.

## Completed geometric integration

The finite induction, including unmatched old and new components, is now
proved in `ComponentChartInduction.lean` and retains the source trace and
block-count bound. `ComponentTraceDichotomy.lean` gives the full-`K_M`
alternative or proper masks in that same trace.
`NormalizedTraceSeparatedTest.lean` identifies the proper trace with a
literal smaller `SeparatedChains` test, including the actual builder,
genuine edges, and completed actions.
`ChainRestrictionNormalForm.lean` combines these results into the
restriction theorem for the original bounded separated-chain test, with
no increase in its block count. No abstract historical-parameter converse
or arbitrary unverified equivariant cover is used here.

The simultaneous augmented recursive record is a separate construction
from this geometric theorem. The follow-up `AugmentedFamilyData.lean`,
`AugmentedFamilyActions.lean`, and `AugmentedFamilyLinks.lean` now construct
that family and verify that its earlier records contain all the required
smaller test actions. This property is not assumed for arbitrary old
records by the component-chart theorem.

## Validation

The source compiled locally on Lean 4.35.0-rc3 with exit code 0 on
17 November 2026. The `.olean` was produced successfully. The durable
`scripts/CheckMatchedComponentLastChartAxioms.lean` manifest audits the
initial chart, complete interface chart,
derived separation, last-coordinate theorem, genuine-edge theorem,
matched extension, and completed-action theorem. These seven exact named
declarations report only `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry` or `admit` declarations. This manifest does not assert
a remote CI result or completion of the main Part II theorem.
