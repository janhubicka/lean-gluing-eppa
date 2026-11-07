import GluingEPPA.BinaryOrbitPaddedWitness

/-!
# The global colour-shift lemma for the one-relation six-colour template

The core fact is finite: if an induced partial map preserves the
single directed relation on all pairs of its domain, then it acts on
the six colours by ONE element of C4. The two finite anchor lemmas
reduce the arbitrary input to the 6-element palette.
-/

namespace GluingEPPA.BinaryOrbitNoncoherence

universe u

theorem palette_point_transitive :
    ∀ a b : Fin 6,
      (templateRel a a ↔ templateRel b b) →
      ∃ k : Fin 4, shift6 k a = b := by
  decide

theorem palette_long_anchor_determines :
    ∀ a b c d : Fin 6, ∀ k : Fin 4,
      templateRel a a →
      (templateRel a a ↔ templateRel b b) →
      (templateRel c c ↔ templateRel d d) →
      (templateRel a c ↔ templateRel b d) →
      (templateRel c a ↔ templateRel d b) →
      shift6 k a = b →
      shift6 k c = d := by
  decide

theorem palette_short_anchor_determines :
    ∀ a b c d : Fin 6, ∀ k : Fin 4,
      ¬ templateRel a a →
      ¬ templateRel c c →
      (templateRel a a ↔ templateRel b b) →
      (templateRel c c ↔ templateRel d d) →
      (templateRel a c ↔ templateRel b d) →
      shift6 k a = b →
      shift6 k c = d := by
  decide

/-- Every relation-preserving partial map of an arbitrary coloured
    set is induced by a single C4-shift on its domain. No finiteness
    assumption on the vertex type is needed. -/
theorem partial_relation_map_has_global_shift
    {A : Type u} (colour : A → Fin 6)
    (p : A → Option A)
    (hrel : ∀ x x' y y',
      p x = some y → p x' = some y' →
      (templateRel (colour x) (colour x') ↔
       templateRel (colour y) (colour y'))) :
    ∃ k : Fin 4, ∀ x y, p x = some y →
      colour y = shift6 k (colour x) := by
  classical
  by_cases hb : ∃ x y, p x = some y ∧ templateRel (colour x) (colour x)
  · obtain ⟨x0, y0, hp0, hl0⟩ := hb
    have hdiag0 := hrel x0 x0 y0 y0 hp0 hp0
    obtain ⟨k, hk⟩ :=
      palette_point_transitive (colour x0) (colour y0) hdiag0
    refine ⟨k, ?_⟩
    intro x y hxy
    have hdiag := hrel x x y y hxy hxy
    have hfwd := hrel x0 x y0 y hp0 hxy
    have hback := hrel x x0 y y0 hxy hp0
    exact (palette_long_anchor_determines
      (colour x0) (colour y0) (colour x) (colour y) k
      hl0 hdiag0 hdiag hfwd hback hk).symm
  · by_cases hsome : ∃ x y, p x = some y
    · obtain ⟨x0, y0, hp0⟩ := hsome
      have hno0 : ¬ templateRel (colour x0) (colour x0) := by
        intro h
        exact hb ⟨x0, y0, hp0, h⟩
      have hdiag0 := hrel x0 x0 y0 y0 hp0 hp0
      obtain ⟨k, hk⟩ :=
        palette_point_transitive (colour x0) (colour y0) hdiag0
      refine ⟨k, ?_⟩
      intro x y hxy
      have hno : ¬ templateRel (colour x) (colour x) := by
        intro h
        exact hb ⟨x, y, hxy, h⟩
      have hdiag := hrel x x y y hxy hxy
      have hfwd := hrel x0 x y0 y hp0 hxy
      exact (palette_short_anchor_determines
        (colour x0) (colour y0) (colour x) (colour y) k
        hno0 hno hdiag0 hdiag hfwd hk).symm
    · refine ⟨0, ?_⟩
      intro x y hxy
      exact False.elim (hsome ⟨x, y, hxy⟩)

/-- Fully general positive EPPA construction, conditional only on
    injectivity and pairwise relation preservation of the partial map.
    The global shift is deduced in the preceding theorem. -/
theorem exists_exact_extension_of_partial_relation_map
    {A : Type u} [Finite A] (colour : A → Fin 6)
    (p : A → Option A)
    (hinj : ∀ x y z, p x = some z → p y = some z → x = y)
    (hrel : ∀ x x' y y',
      p x = some y → p x' = some y' →
      (templateRel (colour x) (colour x') ↔
       templateRel (colour y) (colour y'))) :
    ∃ h : PaddedWitness A ≃ PaddedWitness A,
      (∀ v w, (templateRel (h v).1 (h w).1 ↔
                 templateRel v.1 w.1)) ∧
      (∀ x y, (h (paddedRoot colour x) =
                  paddedRoot colour y ↔ p x = some y)) := by
  obtain ⟨k, hk⟩ := partial_relation_map_has_global_shift colour p hrel
  obtain ⟨h, hshift, hoverlap⟩ :=
    exists_padded_exact_extension colour k p hinj hk
  refine ⟨h, ?_, hoverlap⟩
  intro v w
  rw [hshift v, hshift w]
  exact shift6_preserves k v.1 w.1

end GluingEPPA.BinaryOrbitNoncoherence
