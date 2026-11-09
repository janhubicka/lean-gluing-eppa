import GluingEPPA.Steiner.ChainValuation.HistoricalSupportLastChart

/-!
# Transfer of historical component supports for newly attached vertices

The full support induction needs both kinds of roots. A point in the
new Cayley block either reaches the attaching interface or does not.

The first case connects the new root to a literal old-chain point.
The second cannot reach any old historical block; this follows
from the previously verified canonical matching of actual M-component
classes, not from an unproved informal no-crossing assertion.

The lemmas are independent of the finite-list interval induction.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]

/-- Two points in one M-component meet exactly the same historical
blocks, with their whole ordered support lists equal. -/
theorem historicalSupport_eq_of_reach
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (history : List (HistoricalBlock A C M))
    (q q' : C.Space)
    (hqq' : LabelReach (fun e => (C.matching e).Rel) M q q') :
    historicalSupport A C M history q =
      historicalSupport A C M history q' := by
  induction history with
  | nil => rfl
  | cons T ts ih =>
    have hT : T.Meets A C M q ↔ T.Meets A C M q' := by
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, LabelReach.trans (LabelReach.symm hqq') hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, LabelReach.trans hqq' hx⟩
    change
      T.Meets A C M q :: historicalSupport A C M ts q =
      T.Meets A C M q' :: historicalSupport A C M ts q'
    exact congrArg₂ (fun p ps => p :: ps) (propext hT) ih

/-- A newly attached point reaches an old-chain point only if its
M-component reaches an actual attaching parameter. All paths are
genuine paths in the completed matching of ChainState.extend. -/
theorem extended_newToOldReach_has_interface
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (y : B.Carrier) (x : C.Space)
    (hpath :
      LabelReach
        (fun e => ((extend A B C h left right hl hr hsep hshared).matching e).Rel)
        M (newEmbed A B C h left right hl hr y)
          (oldEmbed A B C h left right hl hr x)) :
    ∃ k : K,
      LabelReach (fun e => (B.matching e).Rel) M y (right k) := by
  let RX := labelReachSetoid (fun e => (C.matching e).Rel) M
  let RY := labelReachSetoid (fun e => (B.matching e).Rel) M
  let f := attachInto C.lastEmbed h left
  let P := canonicalAttachmentMatching RX RY f right hpull
  have hglued : GluedReach RX RY f right (.inr y) (.inl x) :=
    (chainState_extend_reach_iff_glued
      A B C h left right hl hr hsep hshared M
      (.inr y) (.inl x)).mp hpath
  have heq :
      componentClass RX RY P (.inr y) =
        componentClass RX RY P (.inl x) :=
    (gluedReach_iff_canonical_matching
      RX RY f right hpull (.inr y) (.inl x)).mp hglued
  have hpair := (P.quotient_eq_iff
      (Sum.inr (Quotient.mk RY y))
      (Sum.inl (Quotient.mk RX x))).mp heq
  rcases hpair with hequal | hmatch
  · cases hequal
  · change AttachmentComponentPair RX RY f right
      (Quotient.mk RX x) (Quotient.mk RY y) at hmatch
    obtain ⟨k, _, hk⟩ := hmatch
    exact ⟨k, Quotient.exact hk.symm⟩

/-- If the new root does not reach an attaching point, its component
misses every transported old historical Cayley block. -/
theorem HistoricalBlock.transport_new_unmatched
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (T : HistoricalBlock A C M) (y : B.Carrier)
    (hnomeet : ∀ k : K,
      ¬ LabelReach (fun e => (B.matching e).Rel) M y (right k)) :
    ¬ (T.transport A B C h left right hl hr hsep hshared M hpull).Meets
      B (extend A B C h left right hl hr hsep hshared) M
      (newEmbed A B C h left right hl hr y) := by
  rintro ⟨x, hx⟩
  have hreach :
      LabelReach
        (fun e => ((extend A B C h left right hl hr hsep hshared).matching e).Rel)
        M (newEmbed A B C h left right hl hr y)
          (oldEmbed A B C h left right hl hr (T.chart.embed x)) := hx
  obtain ⟨k, hk⟩ := extended_newToOldReach_has_interface
    A B C h left right hl hr hsep hshared M hpull
    y (T.chart.embed x) hreach
  exact hnomeet k hk

/-- Conversely, if the newly attached root reaches the parameter k,
it is connected in the actual extended chain to the old attachment
point indexed by k. This is the matched new-root induction case. -/
theorem extended_newRoot_reach_old_interface
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (y : B.Carrier) (k : K)
    (hyk : LabelReach (fun e => (B.matching e).Rel) M y (right k)) :
    LabelReach
      (fun e => ((extend A B C h left right hl hr hsep hshared).matching e).Rel)
      M (newEmbed A B C h left right hl hr y)
        (oldEmbed A B C h left right hl hr
          (attachInto C.lastEmbed h left k)) := by
  exact (chainState_extend_reach_iff_glued
    A B C h left right hl hr hsep hshared M
    (.inr y) (.inl (attachInto C.lastEmbed h left k))).mpr
      (GluedReach.trans (GluedReach.new hyk)
        (GluedReach.symm (GluedReach.attach k)))

end GluingEPPA.Steiner.ChainValuation
