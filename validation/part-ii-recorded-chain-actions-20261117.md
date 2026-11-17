# Recorded smaller tests give the required chain actions

`RecordedChainActions.lean` and its eleven-declaration axiom manifest pass
the pinned Lean compiler. The manifest permits only `propext`,
`Classical.choice`, and `Quot.sound`. No existing proof source or umbrella
import was changed for this module.

## What is proved

`AugmentedStep.recordedTestAction` is the action of the actual augmented
group on one of its appended permutation coordinates. Its definition reads
`MulOpposite.unop (g.val.2 j)`. The right-action laws follow from the
opposite-product convention, and `recordedTestAction_edge` identifies its
allowed generators with the actual recorded permutations. Consequently
`recordedTest_kernel` derives word-kernel compatibility directly from the
record, without assuming it.

`LinkChain.chainTest_equivariant_cover` applies the checked completed-action
normal form to every point of an actual bounded separated chain. Its source
is either the actual earlier Cayley group or an actual earlier separated
chain with the same bound `N`. The cover commutes with every letter in the
smaller alphabet, including points fixed by matching completion.

The Cayley source carries ordinary right multiplication. Proper sources
carry their already recorded smaller-stage actions. `coveredTest_kernel`
then transfers equality of allowed word values to equality of permutations
on the entire current chain. `chainTestRightAction` reconstructs the earlier
group action, and `chainTestRightAction_edge` gives exactly the `B`/`hB`
interface required by `AugmentedStep.link`.

The generic bridge accepts actions on the tests at the smaller stage `M`.
It does **not** accept an action or word-kernel theorem on the larger
`S`-chain test as a premise. All generator equations are correctly restricted
to letters in `M`; no equation for a letter outside the acting alphabet is
claimed.

## Review of the actual recursive instantiation

The companion `AugmentedFamily` construction discharges the smaller-action
premise using an equality of the actual recursive `Data` with its literal
augmented record. This equality transports the carrier, group structure,
named generators, and recorded coordinate together. It does not replace the
earlier group by an independently chosen isomorphic group.

The source review checked the following points:

- `family_links` uses strong induction only at proper target subsets.
- The same `N` is used in the family, each restricted chain test, each
  recorded action, and every application of the component normal form.
- `smallerOld` is the actual family on the lifted subsets, and
  `smallerLinks` restricts the same predecessor Link family.
- `Link.eq_of_generator_rules` proves uniqueness from word generation and
  the two homomorphisms' generator equations. This removes differences
  between selected predecessor Link witnesses in `tests_eq`.
- Smaller-chain actions come from `recordedAction_exists`, which rewrites
  the exact family-stage equality and applies the literal coordinate action.
- The old component actions are independently obtained by composing
  `Step.action` with the augmented record's forgetful homomorphism.
- Once `family_links` is available, `actual_tests_eq` supplies predecessor
  Links at every actual stage. The empty fallback package is therefore
  absent on actual recursive inputs, including the empty edge set.

No circular use of the current-stage Link, no increased chain bound, and no
assumption equivalent to the target larger-test kernel were found in this
review. The kernel checks and the final combined axiom audit remain the
authoritative formal validation.
