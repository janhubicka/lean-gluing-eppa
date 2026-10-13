import GluingEPPA.PrivateCycles

/-!
The private-cycle permutations really distinguish every inverse-indexed
label, including opposite orientations of an inverse pair. Together with
privateSlots_card this is the linear-marker replacement for ZMod4.
-/
namespace GluingEPPA
universe u
namespace InverseLabels
variable {I : Type u} (D : InverseLabels I) [LinearOrder I]

theorem privatePerm_self_first (i : I) (h : D.inv i = i) :
    D.privatePerm i (i, false) = (i, true) := by
  classical
  simp [privatePerm, h]

theorem privatePerm_nonself_first (i : I) (h : D.inv i ≠ i) :
    D.privatePerm i (i, false) = (D.inv i, false) := by
  classical
  by_cases hl : i < D.inv i
  · have he : D.privatePerm i = privateCycle i (D.inv i) := by
      simp [privatePerm, h, hl]
    rw [he]
    exact privateCycle_first i (D.inv i)
  · have he : D.privatePerm i = (privateCycle (D.inv i) i).symm := by
      simp [privatePerm, h, hl]
    rw [he]
    exact (Equiv.symm_apply_eq).2
      (privateCycle_first (D.inv i) i).symm

theorem privatePerm_moves (i : I) :
    D.privatePerm i (i, false) ≠ (i, false) := by
  by_cases hs : D.inv i = i
  · rw [D.privatePerm_self_first i hs]
    simp
  · rw [D.privatePerm_nonself_first i hs]
    intro he
    exact hs (Prod.mk.inj he).1

theorem privatePerm_fixes_other (i j : I) (b : Bool)
    (hi : i ≠ j) (hj : i ≠ D.inv j) :
    D.privatePerm j (i, b) = (i, b) := by
  classical
  by_cases hs : D.inv j = j
  · have he : D.privatePerm j = Equiv.swap (j, false) (j, true) := by
      simp [privatePerm, hs]
    rw [he]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      exact hi (congrArg Prod.fst h)
    · intro h
      exact hi (congrArg Prod.fst h)
  · by_cases hl : j < D.inv j
    · have he : D.privatePerm j = privateCycle j (D.inv j) := by
        simp [privatePerm, hs, hl]
      rw [he]
      exact privateCycle_fix j (D.inv j) i b hi hj
    · have he : D.privatePerm j = (privateCycle (D.inv j) j).symm := by
        simp [privatePerm, hs, hl]
      rw [he]
      exact (Equiv.symm_apply_eq).2
        (privateCycle_fix (D.inv j) j i b hj hi).symm

/-- An inverse pair has two different directions on its common support. -/
theorem privatePerm_inverse_pair_ne (i : I) (hs : D.inv i ≠ i) :
    D.privatePerm i ≠ D.privatePerm (D.inv i) := by
  intro he
  have hfirst := D.privatePerm_nonself_first i hs
  have hsame : D.privatePerm i (i, false) =
      D.privatePerm (D.inv i) (i, false) := congrArg (fun f => f (i, false)) he
  rw [hfirst] at hsame
  have hrev : i ≠ D.inv i := Ne.symm hs
  have hs2 : D.inv (D.inv i) ≠ D.inv i := by
    rw [D.inv_inv]
    exact hrev
  by_cases hl : i < D.inv i
  · have hnlt : ¬ D.inv i < i := not_lt.mpr (le_of_lt hl)
    have hperm : D.privatePerm (D.inv i) =
        (privateCycle i (D.inv i)).symm := by
      simp [privatePerm, D.inv_inv, hs, hs2, hrev, hl, hnlt]
    rw [hperm] at hsame
    have hp : (privateCycle i (D.inv i)).symm (i, false) = (i, true) :=
      (Equiv.symm_apply_eq).2
        (privateCycle_middle i (D.inv i) hrev).symm
    rw [hp] at hsame
    exact hrev (Prod.mk.inj hsame).1.symm
  · have hgt : D.inv i < i := (lt_or_gt_of_ne hrev).resolve_left hl
    have hperm : D.privatePerm (D.inv i) =
        privateCycle (D.inv i) i := by
      simp [privatePerm, D.inv_inv, hs, hs2, hrev, hl, hgt]
    rw [hperm, privateCycle_last (D.inv i) i hs] at hsame
    exact Bool.false_ne_true (Prod.mk.inj hsame).2

/-- Distinct labels determine distinct nonidentity permutations on 2|I| slots. -/
theorem privatePerm_injective : Function.Injective D.privatePerm := by
  intro i j he
  by_contra hne
  by_cases hji : j = D.inv i
  · subst j
    have hs : D.inv i ≠ i := by
      intro h
      exact hne h.symm
    exact (D.privatePerm_inverse_pair_ne i hs) he
  · have hi : i ≠ j := hne
    have hother : i ≠ D.inv j := by
      intro hh
      apply hji
      calc
        j = D.inv (D.inv j) := (D.inv_inv j).symm
        _ = D.inv i := congrArg D.inv hh.symm
    have hf := D.privatePerm_fixes_other i j false hi hother
    have hx := congrArg (fun f => f (i, false)) he
    rw [hf] at hx
    exact D.privatePerm_moves i hx

theorem privatePerm_ne_refl (i : I) : D.privatePerm i ≠ Equiv.refl _ := by
  intro h
  have hfirst : D.privatePerm i (i, false) = (i, false) :=
    congrArg (fun f => f (i, false)) h
  exact D.privatePerm_moves i hfirst

end InverseLabels
end GluingEPPA
