import GluingEPPA.Steiner.ChainValuation.HistoricalBlockCoverage
import GluingEPPA.Steiner.ChainValuation.ChainExtendMatchedComponent

/-!
# Support of an M-component among the actual historical blocks

A component's support is the list of truth values saying which
historical Cayley blocks it meets. A new separated attachment
preserves the support on old historical blocks exactly. The new
last entry is true exactly when the old component meets the
attaching interface.

This is the geometric induction invariant needed for the
consecutive-interval part of finite-chain normalization.
Statements refer to actual named-edge reachability in ChainState.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]

/-- An actual M-component meets the embedded historical group. -/
def HistoricalBlock.Meets
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (T : HistoricalBlock A C M)
    (q : C.Space) : Prop :=
  ∃ x : T.Carrier,
    LabelReach (fun e => (C.matching e).Rel) M q (T.chart.embed x)

/-- A finite list of the historical blocks touched by the M-component
of q, retaining the original block order. -/
def historicalSupport
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (history : List (HistoricalBlock A C M))
    (q : C.Space) : List Prop :=
  history.map (fun T => T.Meets A C M q)

/-- Old historical-block membership is unchanged by an attachment
with the already verified component-pullback condition. -/
theorem HistoricalBlock.transport_meets_iff
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (T : HistoricalBlock A C M) (q : C.Space) :
    (T.transport A B C h left right hl hr hsep hshared M hpull).Meets
      B (extend A B C h left right hl hr hsep hshared) M
      (oldEmbed A B C h left right hl hr q) ↔
      T.Meets A C M q := by
  change
    (∃ x : T.Carrier,
      LabelReach
        (fun e => ((extend A B C h left right hl hr hsep hshared).matching e).Rel)
        M (oldEmbed A B C h left right hl hr q)
        (oldEmbed A B C h left right hl hr (T.chart.embed x))) ↔
    (∃ x : T.Carrier,
      LabelReach (fun e => (C.matching e).Rel) M q (T.chart.embed x))
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (extended_old_reach_iff_original
      A B C h left right hl hr hsep hshared
      M hpull q (T.chart.embed x)).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (extended_old_reach_iff_original
      A B C h left right hl hr hsep hshared
      M hpull q (T.chart.embed x)).mpr hx⟩

/-- The full ordered list of old support bits is unchanged after
transporting every chart to the extended chain. -/
theorem historicalSupport_transport_old
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (history : List (HistoricalBlock A C M)) (q : C.Space) :
    historicalSupport B
      (extend A B C h left right hl hr hsep hshared) M
      (history.map (fun T => T.transport A B C h left right
        hl hr hsep hshared M hpull))
      (oldEmbed A B C h left right hl hr q) =
    historicalSupport A C M history q := by
  induction history with
  | nil => rfl
  | cons T ts ih =>
    change
      ((T.transport A B C h left right hl hr hsep hshared M hpull).Meets
        B (extend A B C h left right hl hr hsep hshared) M
        (oldEmbed A B C h left right hl hr q)) ::
        historicalSupport B
          (extend A B C h left right hl hr hsep hshared) M
          (ts.map (fun T => T.transport A B C h left right
            hl hr hsep hshared M hpull))
          (oldEmbed A B C h left right hl hr q) =
      T.Meets A C M q :: historicalSupport A C M ts q
    exact congrArg₂ (fun p ps => p :: ps)
      (propext (T.transport_meets_iff A B C h left right
        hl hr hsep hshared M hpull q)) ih

/-- An old M-component reaches some point of the newly attached
Cayley block if and only if it reaches an attaching parameter.
This is an exact cross-boundary characterization, not just
surjectivity of the historical cover. -/
theorem lastBlock_meets_iff_attachment
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
    (q : C.Space) :
    (historicalBlock_last B
      (extend A B C h left right hl hr hsep hshared)
      M Q hnew).Meets B
      (extend A B C h left right hl hr hsep hshared)
      M (oldEmbed A B C h left right hl hr q) ↔
    ∃ k : K,
      LabelReach (fun e => (C.matching e).Rel) M
        q (attachInto C.lastEmbed h left k) := by
  let RX := labelReachSetoid (fun e => (C.matching e).Rel) M
  let RY := labelReachSetoid (fun e => (B.matching e).Rel) M
  let f := attachInto C.lastEmbed h left
  let T := canonicalAttachmentMatching RX RY f right hpull
  change
    (∃ y : B.Carrier,
      LabelReach
        (fun e => ((extend A B C h left right hl hr hsep hshared).matching e).Rel)
        M (oldEmbed A B C h left right hl hr q)
        (newEmbed A B C h left right hl hr y)) ↔
      ∃ k : K, LabelReach (fun e => (C.matching e).Rel) M q (f k)
  constructor
  · rintro ⟨y, hy⟩
    have hglue : GluedReach RX RY f right (.inl q) (.inr y) :=
      (chainState_extend_reach_iff_glued
        A B C h left right hl hr hsep hshared M
        (.inl q) (.inr y)).mp hy
    have hclass :
      componentClass RX RY T (.inl q) =
        componentClass RX RY T (.inr y) :=
      (gluedReach_iff_canonical_matching
        RX RY f right hpull (.inl q) (.inr y)).mp hglue
    have hpair := (T.quotient_eq_iff
      (Sum.inl (Quotient.mk RX q))
      (Sum.inr (Quotient.mk RY y))).mp hclass
    rcases hpair with heq | hmatch
    · cases heq
    · change AttachmentComponentPair RX RY f right
        (Quotient.mk RX q) (Quotient.mk RY y) at hmatch
      obtain ⟨k, hk, _⟩ := hmatch
      exact ⟨k, Quotient.exact hk.symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨right k, ?_⟩
    exact (chainState_extend_reach_iff_glued
      A B C h left right hl hr hsep hshared M
      (.inl q) (.inr (right k))).mpr
        (GluedReach.trans (GluedReach.old hk)
          (GluedReach.attach k))

/-- The support of an old M-component in the extended historical
list is exactly its old support, followed by one final bit indicating
whether it meets the new attaching interface. -/
theorem historicalSupport_extend_old
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
    (history : List (HistoricalBlock A C M)) (q : C.Space) :
    historicalSupport B
      (extend A B C h left right hl hr hsep hshared) M
      (historicalBlocks_extend A B C h left right hl hr
        hsep hshared M hpull Q hnew history)
      (oldEmbed A B C h left right hl hr q) =
    historicalSupport A C M history q ++
      [∃ k : K,
        LabelReach (fun e => (C.matching e).Rel) M
          q (attachInto C.lastEmbed h left k)] := by
  have hsplit :
      historicalSupport B
        (extend A B C h left right hl hr hsep hshared) M
        (historicalBlocks_extend A B C h left right hl hr
          hsep hshared M hpull Q hnew history)
        (oldEmbed A B C h left right hl hr q) =
      historicalSupport B
        (extend A B C h left right hl hr hsep hshared) M
        (history.map (fun T => T.transport A B C h left right
          hl hr hsep hshared M hpull))
        (oldEmbed A B C h left right hl hr q) ++
        [(historicalBlock_last B
          (extend A B C h left right hl hr hsep hshared)
          M Q hnew).Meets B
          (extend A B C h left right hl hr hsep hshared)
          M (oldEmbed A B C h left right hl hr q)] := by
    simp [historicalSupport, historicalBlocks_extend]
  rw [hsplit]
  rw [historicalSupport_transport_old
    A B C h left right hl hr hsep hshared M hpull history q]
  exact congrArg (List.append (historicalSupport A C M history q))
    (congrArg List.singleton
      (propext (lastBlock_meets_iff_attachment
        A B C h left right hl hr hsep hshared M hpull Q hnew q)))

end GluingEPPA.Steiner.ChainValuation
