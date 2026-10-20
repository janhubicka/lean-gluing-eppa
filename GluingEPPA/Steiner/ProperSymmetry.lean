import GluingEPPA.Steiner.FiniteFamily

/-!
# Reindexing proper edge subsets

A graph automorphism sends each proper edge subset to a proper edge subset
of the image. These bijections identify the coordinates of the recursive
finite product before their group actions are transported.
-/

namespace GluingEPPA.Steiner.FiniteFamily

universe u
variable {E : Type u} [DecidableEq E]

theorem finset_image_ssubset (π : E ≃ E) {R S : Finset E}
    (h : R ⊂ S) : R.image π ⊂ S.image π := by
  obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp h
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · exact Finset.image_subset_image hsub
  · intro he
    have hh := congrArg (fun X : Finset E => X.image π.symm) he
    have heq : R = S := by
      simpa only [Finset.image_image, Function.comp_def,
        Equiv.symm_apply_apply, Finset.image_id] using hh
    exact hne heq

noncomputable def properEquiv (π : E ≃ E) (S : Finset E) :
    Proper S ≃ Proper (S.image π) where
  toFun R := ⟨R.val.image π, finset_image_ssubset π R.property⟩
  invFun T := ⟨T.val.image π.symm, by
    have h := finset_image_ssubset π.symm T.property
    simpa only [Finset.image_image, Function.comp_def,
      Equiv.apply_symm_apply, Finset.image_id] using h⟩
  left_inv R := by
    apply Subtype.ext
    ext e
    simp
  right_inv T := by
    apply Subtype.ext
    ext e
    simp

theorem properEquiv_val (π : E ≃ E) (S : Finset E)
    (R : Proper S) :
    (properEquiv π S R).val = R.val.image π := rfl

end GluingEPPA.Steiner.FiniteFamily
