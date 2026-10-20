import GluingEPPA.Steiner.GeneratedStep

/-!
# Relabelling the generated subgroup

An isomorphism between ambient groups mapping the named involutive generators
to their relabelled counterparts restricts to an isomorphism of the generated
subgroups. This is used to construct the symmetry of each new recursive
finite group from the symmetries of its old product coordinates.
-/

namespace GluingEPPA.Steiner

universe u v w z
variable {E : Type u} {F : Type v}
variable {P : Type w} {Q : Type z} [Group P] [Group Q]

namespace GeneratedStep

variable (a : E → P) (b : F → Q)
variable (ha : ∀ e, a e * a e = 1) (hb : ∀ e, b e * b e = 1)
variable (p : P ≃* Q) (σ : E ≃ F)
variable (hgen : ∀ e, p (a e) = b (σ e))
include hgen

theorem map_word (w : List E) :
    wordValue b (w.map σ) = p (wordValue a w) := by
  induction w with
  | nil => simp
  | cons e w ih =>
      simp only [List.map_cons, wordValue_cons, map_mul, ← ih]
      rw [hgen e]

theorem maps_carrier (g : Carrier a ha) :
    p g.val ∈ Carrier b hb := by
  obtain ⟨w, hw⟩ := g.property
  refine ⟨w.map σ, ?_⟩
  calc
    wordValue b (w.map σ) = p (wordValue a w) := map_word a b p σ hgen w
    _ = p g.val := by rw [hw]

theorem inverse_generator : ∀ e, p.symm (b e) = a (σ.symm e) := by
  intro e
  have h := hgen (σ.symm e)
  have hs : p (a (σ.symm e)) = b e := by simpa using h
  have hi := congrArg p.symm hs
  simpa using hi.symm

/-- The isomorphism of the actual finitely generated subgroups. -/
noncomputable def carrierEquiv : Carrier a ha ≃* Carrier b hb where
  toFun g := ⟨p g.val, maps_carrier a b ha hb p σ hgen g⟩
  invFun g :=
    ⟨p.symm g.val,
      maps_carrier b a hb ha p.symm σ.symm
        (inverse_generator a b p σ hgen) g⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    change p (g.val * h.val) = p g.val * p h.val
    exact map_mul p g.val h.val

theorem carrierEquiv_generator (e : E) :
    carrierEquiv a b ha hb p σ hgen (generator a ha e) =
      generator b hb (σ e) := by
  apply Subtype.ext
  exact hgen e

end GeneratedStep
end GluingEPPA.Steiner
