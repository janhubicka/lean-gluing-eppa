import GluingEPPA.Steiner.ComponentCompatibility

/-!
# The invariant component image in the simplified reflection proof

All components and letter permutations are the existing literal Cayley-lift
objects. For a subgroup L of the earlier group, the image consists of actual
components represented by (v,q), q in L. We prove its invariance from the
original two-case letter formula, not from an assumed intersection theorem.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph

universe u v w z
variable {V : Type u} {E : Type v} {H : Type w} [Group H]
variable (D : EdgeGraph V E) (B : Set E) (b : E → H)
variable (hb : ∀ e ∈ B, b e * b e = 1)

/-- Components with a representative whose earlier-group coordinate is in L. -/
def chainComponentImage (L : Subgroup H) : Set (D.Component B b hb) :=
  {c | ∃ v q, q ∈ L ∧ D.component B b hb v q = c}

theorem chainComponentImage_distinguished (L : Subgroup H) (v : V) :
    D.component B b hb v 1 ∈ D.chainComponentImage B b hb L :=
  ⟨v, 1, L.one_mem, rfl⟩

/-- Internal letters multiply within L; external letters only swap two
representatives already in the image. -/
theorem chainComponentImage_edge {A : Set E} (L : Subgroup H)
    (hgen : ∀ e ∈ A, e ∈ B → b e ∈ L)
    {e : E} (he : e ∈ A) {c : D.Component B b hb}
    (hc : c ∈ D.chainComponentImage B b hb L) :
    D.componentEdgePerm B b hb e c ∈ D.chainComponentImage B b hb L := by
  classical
  by_cases heB : e ∈ B
  · obtain ⟨v, q, hq, rfl⟩ := hc
    rw [D.componentEdgePerm_internal_apply B b hb heB]
    exact ⟨v, b e * q, L.mul_mem (hgen e he heB) hq, rfl⟩
  · by_cases hs : c = D.component B b hb (D.source e) 1
    · rw [D.componentEdgePerm_of_not_mem B b hb heB, hs]
      simpa using D.chainComponentImage_distinguished B b hb L (D.target e)
    · by_cases ht : c = D.component B b hb (D.target e) 1
      · rw [D.componentEdgePerm_of_not_mem B b hb heB, ht]
        simpa using D.chainComponentImage_distinguished B b hb L (D.source e)
      · rw [D.componentEdgePerm_external_fixed B b hb heB c hs ht]
        exact hc

/-- Invariance extends to arbitrary words, not only actual base walks. -/
theorem chainComponentImage_word {A : Set E} (L : Subgroup H)
    (hgen : ∀ e ∈ A, e ∈ B → b e ∈ L)
    (w : List E) (hw : ∀ e ∈ w, e ∈ A)
    {c : D.Component B b hb} (hc : c ∈ D.chainComponentImage B b hb L) :
    D.componentWordPerm B b hb w c ∈ D.chainComponentImage B b hb L := by
  induction w generalizing c with
  | nil => exact hc
  | cons e w ih =>
      rw [D.componentWordPerm_cons]
      apply ih (fun f hf => hw f (by simp [hf]))
      exact D.chainComponentImage_edge B b hb L hgen
        (hw e (by simp)) hc

/-- A word wholly in B acts by inverse prefixing on the actual components. -/
theorem chain_componentWord_internal (w : List E)
    (hw : ∀ e ∈ w, e ∈ B) (v : V) (q : H) :
    D.componentWordPerm B b hb w (D.component B b hb v q) =
      D.component B b hb v (((w.map b).prod)⁻¹ * q) := by
  have h := D.componentAction_word B B b hb b
    (D.componentGroupAction B b hb)
    (fun e he c => D.componentGroupAction_edge B b hb he c)
    w hw (D.component B b hb v q)
  exact h.symm

/-- Inclusion of an earlier group preserves the value of its edge words. -/
theorem chain_word_map_value {G : Type z} [Group G]
    (a : E → G) (i : H →* G) (hi : ∀ e ∈ B, i (b e) = a e)
    (w : List E) (hw : ∀ e ∈ w, e ∈ B) :
    i ((w.map b).prod) = (w.map a).prod := by
  induction w with
  | nil => simp
  | cons e w ih =>
      simp only [List.map_cons, List.prod_cons, map_mul]
      rw [hi e (hw e (by simp))]
      rw [ih (fun f hf => hw f (by simp [hf]))]

end EdgeGraph
end GluingEPPA.Steiner
