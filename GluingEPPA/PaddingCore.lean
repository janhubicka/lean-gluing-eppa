import GluingEPPA.PermutationDiagram

/-!
Finite partial bijections admit total permutation extensions; a partial
involution admits an involutive total extension with the complement fixed.
These are the local finite-extension tools used by the labelled marker padding.
-/
namespace GluingEPPA
universe u
variable {A : Type u}

/-- Extend any bijection between two finite subsets to a permutation. -/
theorem exists_perm_extending_partial [Finite A] {p q : A → Prop}
    (f : {x // p x} ≃ {x // q x}) :
    ∃ σ : A ≃ A, ∀ x (hx : p x), σ x = (f ⟨x, hx⟩ : A) := by
  classical
  let source : {x // p x} → A := Subtype.val
  let target : {x // p x} → A := fun x => (f x : A)
  have hs : Function.Injective source := Subtype.val_injective
  have ht : Function.Injective target :=
    Subtype.val_injective.comp f.injective
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair source target hs ht
  refine ⟨σ, ?_⟩
  intro x hx
  exact hσ ⟨x, hx⟩

/-- A partial involution can be extended by the identity outside its domain.
Unlike a generic extension, this gives an actual involution. -/
theorem exists_perm_extending_involution [Finite A] {p : A → Prop}
    (f : {x // p x} ≃ {x // p x}) (hsymm : f.symm = f) :
    ∃ σ : A ≃ A, σ.symm = σ ∧
      ∀ x (hx : p x), σ x = (f ⟨x, hx⟩ : A) := by
  classical
  let g : A → A := fun x => if hx : p x then (f ⟨x, hx⟩ : A) else x
  have hff (x : {x // p x}) : f (f x) = x := by
    have h := f.apply_symm_apply x
    rwa [hsymm] at h
  have hgg : Function.Involutive g := by
    intro x
    by_cases hx : p x
    · have hy : p (g x) := by simpa [g, hx] using (f ⟨x, hx⟩).property
      have heq : (⟨g x, hy⟩ : {x // p x}) = f ⟨x, hx⟩ := by
        apply Subtype.ext
        simp [g, hx]
      change (if hz : p (g x) then (f ⟨g x, hz⟩ : A) else g x) = x
      rw [dite_eq_left hy]
      rw [heq, hff]
    · simp [g, hx]
  let σ : A ≃ A :=
    { toFun := g
      invFun := g
      left_inv := hgg
      right_inv := hgg }
  refine ⟨σ, ?_, ?_⟩
  · apply Equiv.ext
    intro x
    rfl
  · intro x hx
    change g x = (f ⟨x, hx⟩ : A)
    simp [g, hx]
end GluingEPPA
