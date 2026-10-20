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
      ext e
      have he := congrArg (fun U : Finset E => e ∈ U) hh
      simpa using he
    exact hne heq

noncomputable def properEquiv (π : E ≃ E) (S : Finset E) :
    Proper S ≃ Proper (S.image π) where
  toFun R := ⟨R.val.image π, finset_image_ssubset π R.property⟩
  invFun T := ⟨T.val.image π.symm, by
    have h := finset_image_ssubset π.symm T.property
    apply Finset.ssubset_iff_subset_ne.mpr
    obtain ⟨hsub, hne⟩ := Finset.ssubset_iff_subset_ne.mp h
    constructor
    · intro e he
      have he' : e ∈ (S.image π).image π.symm := hsub he
      simpa using he'
    · intro heq
      apply hne
      ext e
      have he' := congrArg (fun U : Finset E => e ∈ U) heq
      simpa using he'⟩
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
