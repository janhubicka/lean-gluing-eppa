import GluingEPPA.Steiner.ChainValuation.Matching

/-!
# Edge-reflecting charts conjugate completed matching involutions

A partial matching is completed to an involutive permutation by
fixing exactly those vertices without a genuine edge. For an
equivalence of vertex sets, *two-way* reflection of the genuine
partial matching relation therefore implies equivariance for the
completed permutation.

This is essential when transporting a normalized M-component chart
to the full word-action interface: one-way edge preservation alone
does not prevent a spurious fixed point or a missing successor.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {X : Type u} {Y : Type v} {E : Type w}

/-- Any edge-reflecting equivalence between partial matchings
conjugates their canonically completed involutive permutations.
No finiteness or missing-edge hypothesis is needed. -/
theorem matching_perm_conjugate_of_rel_iff
    (F : X ≃ Y) (M : Matching X) (N : Matching Y)
    (hRel : ∀ x y, M.Rel x y ↔ N.Rel (F x) (F y))
    (x : X) :
    F (M.perm x) = N.perm (F x) := by
  by_cases h : ∃ y, M.Rel x y
  · obtain ⟨y, hxy⟩ := h
    have hfy : N.Rel (F x) (F y) := (hRel x y).mp hxy
    rw [M.perm_eq_of_rel hxy, N.perm_eq_of_rel hfy]
  · have hn : ¬ ∃ y, N.Rel (F x) y := by
      rintro ⟨y, hxy⟩
      obtain ⟨z, rfl⟩ := F.surjective y
      exact h ⟨z, (hRel x z).mpr hxy⟩
    rw [M.perm_fixed_of_none h, N.perm_fixed_of_none hn]

/-- The same fact for an arbitrary family of named letter matchings:
an equivalence reflecting each genuine e-edge is automatically
equivariant for every completed letter permutation. -/
theorem matching_family_perm_equivariant
    (F : X ≃ Y) (R : E → Matching X) (T : E → Matching Y)
    (hRel : ∀ e x y, (R e).Rel x y ↔
      (T e).Rel (F x) (F y))
    (e : E) (x : X) :
    F ((R e).perm x) = (T e).perm (F x) :=
  matching_perm_conjugate_of_rel_iff F (R e) (T e)
    (hRel e) x

end GluingEPPA.Steiner.ChainValuation
