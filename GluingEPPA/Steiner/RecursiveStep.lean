import GluingEPPA.Steiner.GeneratedStep

/-!
# The product and edge actions for one recursive finite step

This module supplies the literal product used in Lemma 2.2 and proves its
finiteness and generator involutions. The old group/action homomorphisms are
assembled coordinatewise, then `GeneratedStep` constructs the new embeddings.
The full dependent induction over all finite edge subsets remains separate.
-/

namespace GluingEPPA.Steiner

universe u v w z t
attribute [local instance] Classical.propDecidable

namespace Transport

variable {V : Type u} {E : Type v} {G : Type w} [Group G]
variable (T : Transport V G)

/-- The permutations in equation (2) of the paper. The inverse right action
 uses Mathlib's ordinary permutation multiplication. -/
noncomputable def edgePerm (D : EdgeGraph V E) (R : Set E) (a : E → G)
    (e : E) : Equiv.Perm T.Space := by
  classical
  exact if e ∈ R then T.action (a e)
    else T.swapPoints (D.source e) (D.target e)

theorem edgePerm_involutive (D : EdgeGraph V E) (R : Set E) (a : E → G)
    (ha : ∀ e ∈ R, a e * a e = 1) (e : E) :
    T.edgePerm D R a e * T.edgePerm D R a e = 1 := by
  classical
  by_cases he : e ∈ R
  · simp only [edgePerm, ite_eq_left he, ← map_mul, ha e he, map_one]
  · apply Equiv.ext
    intro x
    simp [edgePerm, he, swapPoints]

theorem edgePerm_endpoint (D : EdgeGraph V E) (R : Set E) (a : E → G)
    (ha : ∀ e ∈ R, a e * a e = 1)
    (hstep : ∀ e ∈ R, ∀ u v, D.Joins e u v → T.Rel u v (a e))
    {e : E} {u v : V} (hj : D.Joins e u v) :
    T.edgePerm D R a e (T.marked u) = T.marked v := by
  classical
  by_cases he : e ∈ R
  · have h := (T.action_inv_marked_iff u v (a e)).mpr (hstep e he u v hj)
    simpa only [edgePerm, ite_eq_left he, involutive_inv_eq (ha e he)] using h
  · rcases hj with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · rw [← hu, ← hv]
      simp [edgePerm, he, swapPoints]
    · rw [← hu, ← hv]
      simp [edgePerm, he, swapPoints]

end Transport

namespace RecursiveStep

variable {I : Type u} {V : Type v} {E : Type w}
variable (A : I → Type z) [∀ i, Group (A i)]
variable (T : ∀ i, Transport V (A i))

abbrev Product := ∀ i, A i × Equiv.Perm (T i).Space

instance [Finite I] [Finite V] [∀ i, Finite (A i)] :
    Finite (Product A T) := inferInstance

noncomputable def edgeValue (R : I → Set E) (a : ∀ i, E → A i)
    (D : EdgeGraph V E) (e : E) : Product A T := by
  classical
  exact fun i => (if e ∈ R i then a i e else 1,
    (T i).edgePerm D (R i) (a i) e)

theorem edgeValue_involutive (R : I → Set E) (a : ∀ i, E → A i)
    (D : EdgeGraph V E) (ha : ∀ i e, e ∈ R i → a i e * a i e = 1)
    (e : E) : edgeValue A T R a D e * edgeValue A T R a D e = 1 := by
  classical
  funext i
  apply Prod.ext
  · by_cases he : e ∈ R i
    · simpa [edgeValue, he] using ha i e he
    · simp [edgeValue, he]
  · exact (T i).edgePerm_involutive D (R i) (a i) (ha i) e

/-- Assemble the smaller-group maps into all the old group and permutation
coordinates. No compatibility beyond the given generator equalities is hidden. -/
def coordinateHom {H : Type t} [Group H]
    (f : ∀ i, H →* A i) (ρ : ∀ i, H →* Equiv.Perm (T i).Space) :
    H →* Product A T where
  toFun h i := (f i h, ρ i h)
  map_one' := by
    funext i
    exact Prod.ext (map_one (f i)) (map_one (ρ i))
  map_mul' g h := by
    funext i
    exact Prod.ext (map_mul (f i) g h) (map_mul (ρ i) g h)

/-- The compatibility needed by `GeneratedStep.inclusion` is checked in
 each of the two kinds of coordinates. -/
theorem coordinateHom_generator {H : Type t} [Group H]
    (f : ∀ i, H →* A i) (ρ : ∀ i, H →* Equiv.Perm (T i).Space)
    (R : I → Set E) (a : ∀ i, E → A i) (D : EdgeGraph V E)
    {F : Type w} (b : F → H) (j : F → E)
    (hf : ∀ e i, f i (b e) = if j e ∈ R i then a i (j e) else 1)
    (hρ : ∀ e i, ρ i (b e) = (T i).edgePerm D (R i) (a i) (j e))
    (e : F) :
    coordinateHom A T f ρ (b e) = edgeValue A T R a D (j e) := by
  classical
  funext i
  exact Prod.ext (hf e i) (hρ e i)

def groupProjection (i : I) : Product A T →* A i where
  toFun g := (g i).1
  map_one' := rfl
  map_mul' _ _ := rfl

def actionProjection (i : I) : Product A T →* Equiv.Perm (T i).Space where
  toFun g := (g i).2
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem actionProjection_edgeValue (R : I → Set E)
    (a : ∀ i, E → A i) (D : EdgeGraph V E) (e : E) (i : I) :
    actionProjection A T i (edgeValue A T R a D e) =
      (T i).edgePerm D (R i) (a i) e := rfl

theorem groupProjection_edgeValue (R : I → Set E)
    (a : ∀ i, E → A i) (D : EdgeGraph V E) (e : E) (i : I) :
    groupProjection A T i (edgeValue A T R a D e) =
      if e ∈ R i then a i e else 1 := rfl

/-- The concrete generated group is finite when the old groups and graph are.
The generation and embedding theorems are `GeneratedStep.generated`,
`GeneratedStep.inclusion_injective`, and `GeneratedStep.replacement`. -/
theorem generated_finite [Finite I] [Finite V] [∀ i, Finite (A i)]
    (R : I → Set E) (a : ∀ i, E → A i) (D : EdgeGraph V E)
    (ha : ∀ i e, e ∈ R i → a i e * a i e = 1) :
    Finite (GeneratedStep.Carrier (edgeValue A T R a D)
      (edgeValue_involutive A T R a D ha)) := inferInstance

end RecursiveStep
end GluingEPPA.Steiner
