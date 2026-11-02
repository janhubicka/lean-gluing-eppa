import GluingEPPA.Steiner.ChainValuation.Cosets

/-!
# Local algebra of separated coset cycles

This file checks the incomparability argument used before unrolling a short
coset cycle.  It is independent of the finite chain quotient itself.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u
variable {G : Type u} [Group G]

/-- A separated link cannot have its current subgroup contained in the next
one. Otherwise the current base point lies in both separating cosets. -/
theorem separated_link_not_le
    {Hprev H Hnext : Subgroup G} {g h : G}
    (hconn : h ∈ leftCoset H g)
    (hsep : Disjoint
      (leftCoset (Hprev ⊓ H) g)
      (leftCoset (H ⊓ Hnext) h)) :
    ¬ H ≤ Hnext := by
  intro hle
  have hinf : H ⊓ Hnext = H := inf_eq_left.mpr hle
  have hgFirst : g ∈ leftCoset (Hprev ⊓ H) g :=
    self_mem_leftCoset _ _
  have hcoset : leftCoset H g = leftCoset H h :=
    leftCoset_eq_of_mem hconn
  have hgSecond : g ∈ leftCoset (H ⊓ Hnext) h := by
    rw [hinf, ← hcoset]
    exact self_mem_leftCoset H g
  exact Set.disjoint_left.1 hsep hgFirst hgSecond

/-- Symmetrically, separation at the next link prevents inclusion in the
previous subgroup when connectivity is read backwards. -/
theorem separated_link_not_ge
    {Hprev H Hnext : Subgroup G} {g h : G}
    (hconn : h ∈ leftCoset H g)
    (hsep : Disjoint
      (leftCoset (Hprev ⊓ H) g)
      (leftCoset (H ⊓ Hnext) h)) :
    ¬ H ≤ Hprev := by
  intro hle
  have hinf : Hprev ⊓ H = H := inf_eq_right.mpr hle
  have hgFirst : h ∈ leftCoset (Hprev ⊓ H) g := by
    rw [hinf]
    exact hconn
  have hgSecond : h ∈ leftCoset (H ⊓ Hnext) h :=
    self_mem_leftCoset _ _
  exact Set.disjoint_left.1 hsep hgFirst hgSecond

end GluingEPPA.Steiner.ChainValuation
