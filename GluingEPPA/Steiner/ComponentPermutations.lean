import GluingEPPA.Steiner.CayleyComponents

/-!
# The component permutations of the current recursive gluing proof

For an earlier edge set T, an internal edge acts by left deck translation;
an external edge swaps the two distinguished components. These are exactly
the permutations tau_e^T in the manuscript, on the actual component set C_T.
The endpoint identity holds for either orientation of an edge. No recursive
existence theorem or result from Otto's construction is used.

Lean's permutation product uses left composition. `componentWordPerm` uses
`Equiv.trans` to read letters in their written order, as in the manuscript's
right-action convention.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph

attribute [local instance] Classical.propDecidable

universe u v w
variable {V : Type u} {E : Type v} {G : Type w} [Group G]
variable (D : EdgeGraph V E) (T : Set E) (a : E → G)
variable (ha : ∀ e ∈ T, a e * a e = 1)

/-- The literal two-case definition of tau_e^T. -/
noncomputable def componentEdgePerm (e : E) : Equiv.Perm (D.Component T a ha) := by
  classical
  exact if e ∈ T then D.componentTranslationEquiv T a ha (a e)
    else Equiv.swap (D.component T a ha (D.source e) 1)
      (D.component T a ha (D.target e) 1)

theorem componentEdgePerm_of_mem {e : E} (he : e ∈ T) :
    D.componentEdgePerm T a ha e = D.componentTranslationEquiv T a ha (a e) := by
  classical
  simp [componentEdgePerm, he]

theorem componentEdgePerm_of_not_mem {e : E} (he : e ∉ T) :
    D.componentEdgePerm T a ha e =
      Equiv.swap (D.component T a ha (D.source e) 1)
        (D.component T a ha (D.target e) 1) := by
  classical
  simp [componentEdgePerm, he]

/-- Every letter acts involutively on all components, not only marked ones. -/
theorem componentEdgePerm_involutive (e : E) :
    Function.Involutive (D.componentEdgePerm T a ha e) := by
  classical
  intro c
  by_cases he : e ∈ T
  · rw [D.componentEdgePerm_of_mem T a ha he]
    change D.componentTranslation T a ha (a e)
      (D.componentTranslation T a ha (a e) c) = c
    rw [D.componentTranslation_mul, ha e he, D.componentTranslation_one]
  · rw [D.componentEdgePerm_of_not_mem T a ha he]
    simpa using
      (Equiv.swap (D.component T a ha (D.source e) 1)
        (D.component T a ha (D.target e) 1)).left_inv c

/-- An internal letter is precisely the stated deck transformation. -/
theorem componentEdgePerm_internal_apply {e : E} (he : e ∈ T) (u : V) (g : G) :
    D.componentEdgePerm T a ha e (D.component T a ha u g) =
      D.component T a ha u (a e * g) := by
  rw [D.componentEdgePerm_of_mem T a ha he]
  rfl

/-- Equation (endpoint-action), with either orientation of the named edge. -/
theorem componentEdgePerm_endpoint {e : E} {u v : V} (hj : D.Joins e u v) :
    D.componentEdgePerm T a ha e (D.component T a ha u 1) =
      D.component T a ha v 1 := by
  classical
  by_cases he : e ∈ T
  · rw [D.componentEdgePerm_internal_apply T a ha he]
    apply (D.component_eq_iff_value T a ha u v (a e * 1) 1).2
    have hai : (a e)⁻¹ = a e := by
      calc
        (a e)⁻¹ = (a e)⁻¹ * 1 := (mul_one _).symm
        _ = (a e)⁻¹ * (a e * a e) := by rw [ha e he]
        _ = a e := by group
    simpa only [mul_one, hai] using
      (WalkValue.single (D := D) (a := a) he hj)
  · rw [D.componentEdgePerm_of_not_mem T a ha he]
    rcases hj with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · simp [hu, hv]
    · simp [hu, hv]

/-- An external letter fixes every component other than its two marked ones. -/
theorem componentEdgePerm_external_fixed {e : E} (he : e ∉ T)
    (c : D.Component T a ha)
    (hs : c ≠ D.component T a ha (D.source e) 1)
    (ht : c ≠ D.component T a ha (D.target e) 1) :
    D.componentEdgePerm T a ha e c = c := by
  classical
  rw [D.componentEdgePerm_of_not_mem T a ha he]
  simp [Equiv.swap_apply_def, hs, ht, Ne.symm hs, Ne.symm ht]

/-- The permutation of an arbitrary word, whether or not it is a walk. -/
noncomputable def componentWordPerm : List E → Equiv.Perm (D.Component T a ha)
  | [] => Equiv.refl _
  | e :: w => (D.componentEdgePerm T a ha e).trans (componentWordPerm w)

@[simp] theorem componentWordPerm_nil (c : D.Component T a ha) :
    D.componentWordPerm T a ha [] c = c := rfl

@[simp] theorem componentWordPerm_cons (e : E) (w : List E)
    (c : D.Component T a ha) :
    D.componentWordPerm T a ha (e :: w) c =
      D.componentWordPerm T a ha w (D.componentEdgePerm T a ha e c) := rfl

/-- Concatenation acts in the manuscript's left-to-right reading order. -/
theorem componentWordPerm_append (p q : List E) (c : D.Component T a ha) :
    D.componentWordPerm T a ha (p ++ q) c =
      D.componentWordPerm T a ha q (D.componentWordPerm T a ha p c) := by
  induction p generalizing c with
  | nil => rfl
  | cons e p ih =>
      simpa only [List.cons_append, componentWordPerm_cons] using
        ih (D.componentEdgePerm T a ha e c)

/-- An actual base walk retaining its edge word; vertices and edges may repeat. -/
inductive WordWalk (S : Set E) : V → List E → V → Prop
  | nil (u : V) : WordWalk S u [] u
  | cons {u v z : V} {e : E} {w : List E} :
      e ∈ S → D.Joins e u v → WordWalk S v w z → WordWalk S u (e :: w) z

/-- Retaining the word agrees with the existing actual-walk valuation. -/
theorem WordWalk.value {S : Set E} {u v : V} {w : List E}
    (p : D.WordWalk S u w v) :
    D.WalkValue S a u v ((w.map a).prod) := by
  induction p with
  | nil u =>
      simpa using (WalkValue.nil (D := D) (S := S) (a := a) u)
  | cons he hj p ih =>
      simpa only [List.map_cons, List.prod_cons] using (WalkValue.cons he hj ih)

/-- Conversely every previously defined actual valued walk has such a word. -/
theorem WalkValue.exists_word {S : Set E} {u v : V} {g : G}
    (p : D.WalkValue S a u v g) :
    ∃ w, D.WordWalk S u w v ∧ (w.map a).prod = g := by
  induction p with
  | nil u => exact ⟨[], WordWalk.nil u, rfl⟩
  | @cons u v z e g he hj p ih =>
      obtain ⟨w,hw,hv⟩ := ih
      exact ⟨e :: w, WordWalk.cons he hj hw, by
        simp only [List.map_cons, List.prod_cons, hv]⟩

/-- The endpoint identity iterated along a genuine walk, not an arbitrary word. -/
theorem componentWordPerm_walk {S : Set E} {u v : V} {w : List E}
    (p : D.WordWalk S u w v) :
    D.componentWordPerm T a ha w (D.component T a ha u 1) =
      D.component T a ha v 1 := by
  induction p with
  | nil => rfl
  | cons he hj p ih =>
      rw [D.componentWordPerm_cons, D.componentEdgePerm_endpoint T a ha hj]
      exact ih

end EdgeGraph
end GluingEPPA.Steiner
