import GluingEPPA.BinaryOrbitSmallEPPA

/-!
# Extending finite partial colour-shifting maps

The elementary fibrewise extension step in the padded-witness EPPA
argument. This lemma works for an arbitrary finite index type I and
an arbitrary palette C: if the prescribed map is injective and sends
each colour c to σ(c), it extends to a total permutation of C × I
with exactly that colour action.

The remaining EPPA proof must construct a pair of injective embeddings
of each input into its uniformly padded witness and use this lemma.
-/

namespace GluingEPPA.BinaryOrbitNoncoherence

universe u v w

/-- Fibrewise extension of any finite injective matching compatible
    with a prescribed permutation of the colour palette. -/
theorem exists_colour_shift_extension
    {C : Type u} {I : Type v} {D : Type w}
    [Finite I] (σ : C ≃ C) (src tgt : D → C × I)
    (hs : Function.Injective src)
    (ht : Function.Injective tgt)
    (hc : ∀ d, (tgt d).1 = σ ((src d).1)) :
    ∃ h : (C × I) ≃ (C × I),
      (∀ x, (h x).1 = σ x.1) ∧ (∀ d, h (src d) = tgt d) := by
  classical
  let Fibre (c : C) := {d : D // (src d).1 = c}
  have he (c : C) :
      ∃ p : I ≃ I,
        ∀ d : Fibre c, p ((src d.val).2) = (tgt d.val).2 := by
    let srcIndex : Fibre c → I := fun d => (src d.val).2
    let tgtIndex : Fibre c → I := fun d => (tgt d.val).2
    have hsi : Function.Injective srcIndex := by
      intro x y hxy
      apply Subtype.ext
      apply hs
      apply Prod.ext
      · exact x.property.trans y.property.symm
      · exact hxy
    have hti : Function.Injective tgtIndex := by
      intro x y hxy
      apply Subtype.ext
      apply ht
      apply Prod.ext
      · calc
          (tgt x.val).1 = σ ((src x.val).1) := hc x.val
          _ = σ c := congrArg σ x.property
          _ = σ ((src y.val).1) := congrArg σ y.property.symm
          _ = (tgt y.val).1 := (hc y.val).symm
      · exact hxy
    obtain ⟨p, hp⟩ :=
      Equiv.Perm.exists_extending_pair srcIndex tgtIndex hsi hti
    exact ⟨p, hp⟩
  let τ (c : C) : I ≃ I := Classical.choose (he c)
  let h : (C × I) ≃ (C × I) :=
    { toFun := fun x => (σ x.1, τ x.1 x.2)
      invFun := fun y => (σ.symm y.1, (τ (σ.symm y.1)).symm y.2)
      left_inv := by
        intro x
        rcases x with ⟨c, i⟩
        simp
      right_inv := by
        intro x
        rcases x with ⟨c, i⟩
        simp }
  refine ⟨h, ?_, ?_⟩
  · intro x
    rfl
  · intro d
    apply Prod.ext
    · exact (hc d).symm
    · have hd := Classical.choose_spec (he ((src d).1))
      exact hd ⟨d, rfl⟩

end GluingEPPA.BinaryOrbitNoncoherence
