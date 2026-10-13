import GluingEPPA.Marker4

/-!
Sofia's small private-cycle markers.  There are exactly two potential
marker points for each label, but each two-element inversion orbit uses
only three of its four points.  The unused fourth point stays fixed.

This differs from the ZMod4 translation proof, which uses exponentially
many points.  Completing the inverse and injectivity checks will verify
the bound |U| <= |A| + 2|I| in the manuscript.
-/
namespace GluingEPPA
universe u

namespace InverseLabels
variable {I : Type u} (D : InverseLabels I) [LinearOrder I]

abbrev PrivateSlots (I : Type u) := I × Bool

theorem privateSlots_card [Fintype I] :
    Fintype.card (PrivateSlots I) = 2 * Fintype.card I := by
  simp [PrivateSlots, Fintype.card_prod, mul_comm]

/-- A private three-cycle on (i,false), (i,true), (j,false). -/
noncomputable def privateCycle (i j : I) : PrivateSlots I ≃ PrivateSlots I := by
  classical
  exact (Equiv.swap (i, false) (i, true)).trans
    (Equiv.swap (i, true) (j, false))

theorem privateCycle_first (i j : I) :
    privateCycle i j (i, false) = (j, false) := by
  classical
  simp [privateCycle]

theorem privateCycle_middle (i j : I) (h : i ≠ j) :
    privateCycle i j (i, true) = (i, false) := by
  classical
  simp [privateCycle, Equiv.swap_apply_of_ne_of_ne, h, Ne.symm h]

theorem privateCycle_last (i j : I) (h : i ≠ j) :
    privateCycle i j (j, false) = (i, true) := by
  classical
  simp [privateCycle, Equiv.swap_apply_of_ne_of_ne, h, Ne.symm h]

theorem privateCycle_fix (i j k : I) (b : Bool) (hi : k ≠ i) (hj : k ≠ j) :
    privateCycle i j (k, b) = (k, b) := by
  classical
  simp [privateCycle, Equiv.swap_apply_of_ne_of_ne, hi, hj]

/-- Self-inverse labels swap their two private points; a two-label orbit
uses the three-cycle, with opposite orientation for inverse labels. -/
noncomputable def privatePerm (i : I) : PrivateSlots I ≃ PrivateSlots I := by
  classical
  exact if D.inv i = i then
    Equiv.swap (i, false) (i, true)
  else if i < D.inv i then
    privateCycle i (D.inv i)
  else
    (privateCycle (D.inv i) i).symm

theorem privatePerm_inverse (i : I) :
    D.privatePerm (D.inv i) = (D.privatePerm i).symm := by
  classical
  by_cases hs : D.inv i = i
  · rw [hs]
    simp [privatePerm, hs, Equiv.symm_swap]
  · have hs2 : D.inv (D.inv i) ≠ D.inv i := by
      rw [D.inv_inv]
      exact Ne.symm hs
    by_cases hl : i < D.inv i
    · have hnl : ¬ D.inv i < i := not_lt.mpr (le_of_lt hl)
      simp [privatePerm, hs, hs2, D.inv_inv, hl, hnl]
    · have hgt : D.inv i < i :=
        (lt_or_gt_of_ne (Ne.symm hs)).resolve_left hl
      simp [privatePerm, hs, hs2, D.inv_inv, hl, hgt]

end InverseLabels
end GluingEPPA
