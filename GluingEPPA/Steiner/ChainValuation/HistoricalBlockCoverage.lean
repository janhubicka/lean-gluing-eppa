import GluingEPPA.Steiner.ChainValuation.HistoricalBlockFamily

/-!
# Coverage by all historical restricted-coset charts

A finite list of historical block charts is useful for a component
classification only when its images cover *every vertex* of the actual
chain quotient. The original chain begins with one complete Cayley
block. Each exact pushout extension preserves all earlier charts
and contributes one new last-block chart; the exact pushout coverage
lemma therefore proves coverage by induction.

Nothing here assumes an ambient large group or a global N-acyclicity
theorem. The normalized smaller-chain component chart is still open.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]

/-- Every point of the literal chain belongs to the image of one of
the listed (possibly heterogeneous) historical Cayley-block charts. -/
def HistoricalBlocksCover
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E)
    (history : List (HistoricalBlock A C M)) : Prop :=
  ∀ q : C.Space,
    ∃ T : HistoricalBlock A C M,
      T ∈ history ∧ ∃ x : T.Carrier, T.chart.embed x = q

/-- The single original Cayley block covers the initial chain. -/
theorem historicalBlocks_first_cover
    (A : GroupBlock E) (M : Finset E) (P : Subgroup A.Carrier)
    (hinv : LastBlockCosetInvariant A (ChainState.first A) M P) :
    HistoricalBlocksCover A (ChainState.first A) M
      [historicalBlock_last A (ChainState.first A) M P hinv] := by
  intro q
  let T := historicalBlock_last A (ChainState.first A) M P hinv
  refine ⟨T, ?_, q, ?_⟩
  · simp [T]
  · rfl

/-- Transporting all previous historical charts and appending the
new last-block chart continues to cover every actual pushout point. -/
theorem historicalBlocks_extend_cover
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (Q : Subgroup B.Carrier)
    (hnew : LastBlockCosetInvariant B
      (GluingEPPA.Steiner.ChainValuation.extend
        A B C h left right hleft hright hsep hshared) M Q)
    (history : List (HistoricalBlock A C M))
    (hcover : HistoricalBlocksCover A C M history) :
    HistoricalBlocksCover B
      (GluingEPPA.Steiner.ChainValuation.extend
        A B C h left right hleft hright hsep hshared) M
      (historicalBlocks_extend A B C h left right hleft hright
        hsep hshared M hpull Q hnew history) := by
  intro q
  rcases extendedSpace_covered A B C h left right hleft hright q with
    ⟨x, hx⟩ | ⟨y, hy⟩
  · obtain ⟨T, hT, z, hz⟩ := hcover x
    let T' := T.transport A B C h left right hleft hright
      hsep hshared M hpull
    have hmap : T' ∈ history.map
        (fun U => U.transport A B C h left right hleft hright
          hsep hshared M hpull) := by
      exact List.mem_map.mpr ⟨T, hT, rfl⟩
    have hmember : T' ∈ historicalBlocks_extend
        A B C h left right hleft hright hsep hshared
        M hpull Q hnew history := by
      exact List.mem_append.mpr (Or.inl hmap)
    refine ⟨T', hmember, z, ?_⟩
    change oldEmbed A B C h left right hleft hright (T.chart.embed z) = q
    rw [hz]
    exact hx
  · let T' := historicalBlock_last B
        (GluingEPPA.Steiner.ChainValuation.extend
          A B C h left right hleft hright hsep hshared)
        M Q hnew
    have hmember : T' ∈ historicalBlocks_extend
        A B C h left right hleft hright hsep hshared
        M hpull Q hnew history := by
      simp [historicalBlocks_extend, T']
    refine ⟨T', hmember, y, ?_⟩
    change newEmbed A B C h left right hleft hright y = q
    exact hy

end GluingEPPA.Steiner.ChainValuation
