import GluingEPPA.Steiner.ChainValuation.HistoricalBlockCoverage

/-!
# Whole coset intersections of actual M-components with historical blocks

The checked historical chart invariant describes reachability between
two points in a single historical block. Here the reference point
may be any vertex q of the whole chain. If the M-component of q
meets a historical block at x, its entire intersection with that
block is exactly the translated restricted coset through x.

Combined with joint coverage by all the historical charts, this
shows that every vertex of every genuine M-component belongs to
a whole restricted coset of a recorded historical block.

These are statements about actual paths in ChainState, not only
abstract matching classes. The support-interval and normalized
smaller-chain chart conclusions remain separate tasks.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {H : Type v} [Group H]

/-- An actual M-component meets a historical block in either no points
or in a full left coset, even if the component was anchored at a
point elsewhere in the final chain. -/
theorem HistoricalCosetChart.component_slice_of_meets
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (P : Subgroup H)
    (T : HistoricalCosetChart A C M P)
    (q : C.Space) (x : H)
    (hqx : LabelReach (fun e => (C.matching e).Rel) M
      q (T.embed x)) :
    {y : H | LabelReach (fun e => (C.matching e).Rel) M
      q (T.embed y)} = leftCoset P x := by
  ext y
  constructor
  · intro hqy
    have hxy : LabelReach (fun e => (C.matching e).Rel) M
        (T.embed x) (T.embed y) :=
      LabelReach.trans (LabelReach.symm hqx) hqy
    exact (T.reach_iff x y).mp hxy
  · intro hy
    have hxy : LabelReach (fun e => (C.matching e).Rel) M
        (T.embed x) (T.embed y) :=
      (T.reach_iff x y).mpr hy
    exact LabelReach.trans hqx hxy

/-- Every historical chart's intersection with an actual M-component
is empty or exactly one entire restricted coset. -/
theorem HistoricalCosetChart.component_slice_empty_or_coset
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (P : Subgroup H)
    (T : HistoricalCosetChart A C M P)
    (q : C.Space) :
    {y : H | LabelReach (fun e => (C.matching e).Rel) M
      q (T.embed y)} = ∅ ∨
    ∃ x : H,
      {y : H | LabelReach (fun e => (C.matching e).Rel) M
        q (T.embed y)} = leftCoset P x := by
  classical
  by_cases h : ∃ x : H,
    LabelReach (fun e => (C.matching e).Rel) M q (T.embed x)
  · right
    obtain ⟨x, hx⟩ := h
    exact ⟨x, T.component_slice_of_meets A C M P q x hx⟩
  · left
    ext y
    constructor
    · intro hy
      exact False.elim (h ⟨y, hy⟩)
    · intro hy
      exact False.elim (Set.not_mem_empty y hy)

/-- Joint coverage turns the pointwise coset law into a statement
about every vertex of every actual M-component of a finite chain.
The witness carries the entire coset preimage, not just one point. -/
theorem historicalCover_component_coset
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E)
    (history : List (HistoricalBlock A C M))
    (hcover : HistoricalBlocksCover A C M history)
    (q r : C.Space)
    (hqr : LabelReach (fun e => (C.matching e).Rel) M q r) :
    ∃ T : HistoricalBlock A C M,
      T ∈ history ∧
      ∃ x : T.Carrier,
        T.chart.embed x = r ∧
        (∀ y : T.Carrier,
          LabelReach (fun e => (C.matching e).Rel) M
            q (T.chart.embed y) ↔
          y ∈ leftCoset T.subgroup x) := by
  obtain ⟨T, hT, x, hx⟩ := hcover r
  refine ⟨T, hT, x, hx, ?_⟩
  have hqx : LabelReach (fun e => (C.matching e).Rel) M
      q (T.chart.embed x) := by
    rw [hx]
    exact hqr
  have hslice :=
    T.chart.component_slice_of_meets A C M T.subgroup q x hqx
  intro y
  exact Set.ext_iff.mp hslice y

/-- The full M-component of q is precisely the union of whole
restricted coset pieces from the historical charts that it meets. -/
theorem historicalCover_component_iff_coset_piece
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E)
    (history : List (HistoricalBlock A C M))
    (hcover : HistoricalBlocksCover A C M history)
    (q r : C.Space) :
    LabelReach (fun e => (C.matching e).Rel) M q r ↔
    ∃ T : HistoricalBlock A C M,
      T ∈ history ∧
      ∃ x y : T.Carrier,
        T.chart.embed x = r ∧
        LabelReach (fun e => (C.matching e).Rel) M
          q (T.chart.embed y) ∧
        x ∈ leftCoset T.subgroup y := by
  constructor
  · intro hqr
    obtain ⟨T, hT, x, hx⟩ := hcover r
    refine ⟨T, hT, x, x, hx, ?_, ?_⟩
    · rw [hx]
      exact hqr
    · exact self_mem_leftCoset T.subgroup x
  · rintro ⟨T, hT, x, y, hx, hqy, hcoset⟩
    have hyx : LabelReach (fun e => (C.matching e).Rel) M
        (T.chart.embed y) (T.chart.embed x) :=
      (T.chart.reach_iff y x).mpr hcoset
    have hqr := LabelReach.trans hqy hyx
    rw [hx] at hqr
    exact hqr

end GluingEPPA.Steiner.ChainValuation
