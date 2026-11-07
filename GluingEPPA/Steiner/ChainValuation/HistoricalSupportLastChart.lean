import GluingEPPA.Steiner.ChainValuation.ConsecutiveSupportFinal

/-!
# The actual last Cayley chart discharges the active-suffix condition

The finite historical-chart constructor appends the genuine last block
at every step. We record this precise property as a support-list
witness, including the original one-block base case.

If the support is consecutive, the old component meets the exit
interface, and its history ends in the literal last-block chart,
the support necessarily has an active suffix. Consequently the
consecutive-support invariant is preserved at the actual
ChainState.extend without any additional combinatorial assumption.

These lemmas are about historical charts and labelled components.
The remaining global task is the induction over *all* components,
including those whose root is newly introduced.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]

/-- The historical list ends with the genuine last Cayley chart,
expressed without requiring equality of proof-carrying chart records. -/
def HasLastHistoricalChart
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (history : List (HistoricalBlock A C M)) : Prop :=
  ∀ q : C.Space,
    ∃ prefix : List Prop,
      historicalSupport A C M history q =
        prefix ++
          [∃ x : A.Carrier,
            LabelReach (fun e => (C.matching e).Rel)
              M q (C.lastEmbed x)]

/-- The singleton history of an initial Cayley block ends in its
actual last-block chart. -/
theorem singletonLast_hasLastHistoricalChart
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (P : Subgroup A.Carrier)
    (h : LastBlockCosetInvariant A C M P) :
    HasLastHistoricalChart A C M [historicalBlock_last A C M P h] := by
  intro q
  refine ⟨[], ?_⟩
  rfl

/-- Every actual extended history ends with exactly the newly
attached full Cayley block. No assumption on the old history is needed:
it is the final entry of historicalBlocks_extend by construction. -/
theorem historicalBlocks_extend_hasLast
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (Q : Subgroup B.Carrier)
    (hnew : LastBlockCosetInvariant B
      (extend A B C h left right hl hr hsep hshared) M Q)
    (history : List (HistoricalBlock A C M)) :
    HasLastHistoricalChart B
      (extend A B C h left right hl hr hsep hshared)
      M (historicalBlocks_extend A B C h left right hl hr
        hsep hshared M hpull Q hnew history) := by
  intro q
  let C' := extend A B C h left right hl hr hsep hshared
  let mapped := history.map (fun T =>
    T.transport A B C h left right hl hr hsep hshared M hpull)
  refine ⟨historicalSupport B C' M mapped q, ?_⟩
  have hsplit :
    historicalSupport B C' M
      (historicalBlocks_extend A B C h left right hl hr
        hsep hshared M hpull Q hnew history) q =
    historicalSupport B C' M mapped q ++
      [(historicalBlock_last B C' M Q hnew).Meets B C' M q] := by
    simp [historicalSupport, historicalBlocks_extend, C', mapped]
  rw [hsplit]
  rfl

/-- Reaching the actual exit interface forces the final support
predicate to hold. For a consecutive old component this identifies
its interval with an active suffix. -/
theorem activeSuffix_of_lastChart_and_exit
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (history : List (HistoricalBlock A C M))
    (q : C.Space)
    (hlast : HasLastHistoricalChart A C M history)
    (hinterval : IsConsecutiveSupport (historicalSupport A C M history q))
    (x : A.Carrier)
    (hqx : LabelReach (fun e => (C.matching e).Rel)
      M q (C.lastEmbed x)) :
    IsActiveSuffixSupport (historicalSupport A C M history q) := by
  obtain ⟨prefix, hpref⟩ := hlast q
  rw [hpref]
  apply consecutive_activeSuffix_of_last prefix
    (∃ y : A.Carrier,
      LabelReach (fun e => (C.matching e).Rel)
        M q (C.lastEmbed y))
  · simpa only [← hpref] using hinterval
  · exact ⟨x, hqx⟩

/-- The active-suffix hypothesis from PR #128 is now discharged
using only the genuine last-chart witness and the fact that every
attaching point lies in the old last Cayley block. -/
theorem historicalSupport_extend_old_consecutive_of_lastChart
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (Q : Subgroup B.Carrier)
    (hnew : LastBlockCosetInvariant B
      (extend A B C h left right hl hr hsep hshared) M Q)
    (history : List (HistoricalBlock A C M)) (q : C.Space)
    (hinterval : IsConsecutiveSupport
      (historicalSupport A C M history q))
    (hlast : HasLastHistoricalChart A C M history) :
    IsConsecutiveSupport
      (historicalSupport B
        (extend A B C h left right hl hr hsep hshared) M
        (historicalBlocks_extend A B C h left right hl hr
          hsep hshared M hpull Q hnew history)
        (oldEmbed A B C h left right hl hr q)) := by
  apply historicalSupport_extend_consecutive
    A B C h left right hl hr hsep hshared M hpull Q hnew
    history q hinterval
  rintro ⟨k, hqk⟩
  exact activeSuffix_of_lastChart_and_exit A C M history q
    hlast hinterval (h * left k) hqk

end GluingEPPA.Steiner.ChainValuation
