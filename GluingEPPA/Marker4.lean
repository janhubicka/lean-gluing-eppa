import GluingEPPA.PaddingCore

/-!
A uniform finite marker permutation construction for inverse-indexed labels.

The marker set I → ZMod 4 is larger than the efficient private 2/3-cycle
marker sets in Sofia's manuscript. This construction validates existence,
inverse compatibility, injectivity and nontriviality independently of the
manuscript's sharper 2 * |I| marker bound.
-/
namespace GluingEPPA
universe u

structure InverseLabels (I : Type u) where
  inv : I → I
  inv_inv : ∀ i, inv (inv i) = i

namespace InverseLabels
variable {I : Type u} (D : InverseLabels I) [DecidableEq I]

abbrev Marker (I : Type u) := I → ZMod 4

def step (i : I) : Marker I :=
  fun j =>
    if h : D.inv i = i then
      if j = i then 2 else 0
    else
      (if j = i then 1 else 0) - (if j = D.inv i then 1 else 0)

theorem own_value (i : I) :
    D.step i i = if D.inv i = i then 2 else 1 := by
  by_cases h : D.inv i = i
  · simp [step, h]
  · simp [step, h, Ne.symm h]

theorem other_value (i j : I) (h : i ≠ j) :
    D.step j i = 0 ∨ D.step j i = 3 := by
  by_cases hj : D.inv j = j
  · left
    simp [step, hj, h]
  · by_cases hj' : D.inv j = i
    · right
      simp [step, hj, h, hj']
      norm_num
    · left
      simp [step, hj, h, hj']

theorem step_ne_zero (i : I) : D.step i ≠ 0 := by
  intro h
  have hi := congrFun h i
  rw [D.own_value i] at hi
  by_cases hs : D.inv i = i
  · simp [hs] at hi
  · simp [hs] at hi

theorem step_injective : Function.Injective D.step := by
  intro i j h
  by_contra hne
  have he : D.step i i = D.step j i := congrFun h i
  rcases D.other_value i j hne with hz | hz
  · rw [D.own_value, hz] at he
    by_cases hs : D.inv i = i
    · simp [hs] at he
    · simp [hs] at he
  · rw [D.own_value, hz] at he
    by_cases hs : D.inv i = i
    · norm_num [hs] at he
    · norm_num [hs] at he

theorem step_inverse (i : I) : D.step (D.inv i) = - D.step i := by
  funext j
  by_cases h : D.inv i = i
  · rw [h]
    by_cases hj : j = i
    · simp [step, h, hj] <;> norm_num
    · simp [step, h, hj]
  · have hinv : D.inv (D.inv i) ≠ D.inv i := by
      rw [D.inv_inv]
      exact Ne.symm h
    simp only [step, if_neg h, if_neg hinv, D.inv_inv]
    abel

def translation (D : InverseLabels I) (v : Marker I) :
    Marker I ≃ Marker I where
  toFun x := x + v
  invFun x := x - v
  left_inv := by intro x; simp
  right_inv := by intro x; simp

theorem translation_injective : Function.Injective (D.translation : Marker I → (Marker I ≃ Marker I)) := by
  intro v w h
  have hz : D.translation v 0 = D.translation w 0 := congrArg (fun e => e 0) h
  simpa [translation] using hz

theorem translation_inverse (v : Marker I) :
    D.translation (-v) = (D.translation v).symm := by
  apply Equiv.ext
  intro x
  ext j
  simp [translation, sub_eq_add_neg]

def markerPerm (i : I) : Marker I ≃ Marker I :=
  D.translation (D.step i)

theorem markerPerm_injective : Function.Injective D.markerPerm :=
  D.translation_injective.comp D.step_injective

theorem markerPerm_inverse (i : I) :
    D.markerPerm (D.inv i) = (D.markerPerm i).symm := by
  simp only [markerPerm, D.step_inverse, D.translation_inverse]

theorem markerPerm_ne_refl (i : I) : D.markerPerm i ≠ Equiv.refl _ := by
  intro h
  have hz : D.step i = 0 := by
    have heq : (D.markerPerm i) 0 = (Equiv.refl _) 0 := congrArg (fun e => e 0) h
    simpa [markerPerm, translation] using heq
  exact D.step_ne_zero i hz

end InverseLabels
end GluingEPPA
