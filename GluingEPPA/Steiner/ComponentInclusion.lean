import GluingEPPA.Steiner.ComponentPermutations

/-!
# The smaller-component injection in the current manuscript

This is j_N^T on actual Cayley components. Well-definedness uses only an
edge-preserving homomorphism and N subset T. Injectivity uses precisely
the earlier-stage exact-walk replacement premise; the premise is not
assumed as a theorem about the eventual recursion.

Equivariance and image invariance are proved on all components. They are
the input to the two-part action in the compatibility lemma, not a
replacement for that lemma or a proof of the whole finite recursion.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph

universe u v w z
variable {V : Type u} {E : Type v} {G : Type w} {H : Type z}
variable [Group G] [Group H]

namespace WalkValue
variable {D : EdgeGraph V E} {M : Set E} {a b : E → G}

/-- Values use only the edge values on the allowed edge set. -/
theorem congr_edges (hab : ∀ e ∈ M, a e = b e)
    {u v : V} {g : G} (p : D.WalkValue M a u v g) :
    D.WalkValue M b u v g := by
  induction p with
  | nil => exact WalkValue.nil _
  | @cons u v w e g he hj p ih =>
      simpa only [hab e he] using (WalkValue.cons he hj ih)

end WalkValue

variable (D : EdgeGraph V E) (N T : Set E) (a : E → G) (b : E → H)
variable (ha : ∀ e ∈ N, a e * a e = 1) (hb : ∀ e ∈ T, b e * b e = 1)
variable (hNT : N ⊆ T) (i : G →* H) (hi : ∀ e ∈ N, i (a e) = b e)

/-- The formula c_N(u,g) maps to c_T(u,i(g)), applied to actual components. -/
def componentMap : D.Component N a ha → D.Component T b hb :=
  Quotient.map (fun z : V × G => (z.1, i z.2)) (by
    intro x y p
    apply (D.cayleyWalk_iff_value T b x.1 y.1 (i x.2) (i y.2)).2
    have q := ((p.value.map i).congr_edges hi).mono hNT
    simpa only [map_mul, map_inv] using q)

@[simp] theorem componentMap_apply (u : V) (g : G) :
    D.componentMap N T a b ha hb hNT i hi (D.component N a ha u g) =
      D.component T b hb u (i g) := rfl

@[simp] theorem componentMap_distinguished (u : V) :
    D.componentMap N T a b ha hb hNT i hi (D.component N a ha u 1) =
      D.component T b hb u 1 := by
  simp only [componentMap_apply, map_one]

/-- Exact earlier-stage replacement is the explicit injectivity hypothesis. -/
theorem componentMap_injective
    (hreplace : ∀ u v g, D.WalkValue T b u v (i g) → D.WalkValue N a u v g) :
    Function.Injective (D.componentMap N T a b ha hb hNT i hi) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  rintro ⟨u,g⟩ ⟨v,h⟩ heq
  apply (D.component_eq_iff_value N a ha u v g h).2
  apply hreplace u v (g⁻¹ * h)
  have q := (D.component_eq_iff_value T b hb u v (i g) (i h)).1 heq
  simpa only [map_mul, map_inv] using q

/-- j intertwines every translation by an element of the earlier group. -/
theorem componentMap_translation (k : G) (c : D.Component N a ha) :
    D.componentMap N T a b ha hb hNT i hi (D.componentTranslation N a ha k c) =
      D.componentTranslation T b hb (i k)
        (D.componentMap N T a b ha hb hNT i hi c) := by
  refine Quotient.inductionOn c ?_
  rintro ⟨u,g⟩
  change D.component T b hb u (i (k * g)) =
    D.component T b hb u (i k * i g)
  rw [map_mul]

/-- Every distinguished component belongs to Y = range j. -/
theorem distinguished_mem_componentMap_range (u : V) :
    D.component T b hb u 1 ∈ Set.range (D.componentMap N T a b ha hb hNT i hi) :=
  ⟨D.component N a ha u 1, D.componentMap_distinguished N T a b ha hb hNT i hi u⟩

/-- Earlier-group translations preserve both Y and its complement. -/
theorem componentMap_range_translation (k : G) (c : D.Component T b hb) :
    D.componentTranslation T b hb (i k) c ∈
        Set.range (D.componentMap N T a b ha hb hNT i hi) ↔
      c ∈ Set.range (D.componentMap N T a b ha hb hNT i hi) := by
  constructor
  · rintro ⟨d,hd⟩
    refine ⟨D.componentTranslation N a ha k⁻¹ d, ?_⟩
    rw [D.componentMap_translation, map_inv, hd, D.componentTranslation_mul,
      inv_mul_cancel, D.componentTranslation_one]
  · rintro ⟨d,rfl⟩
    exact ⟨D.componentTranslation N a ha k d,
      D.componentMap_translation N T a b ha hb hNT i hi k d⟩

/-- An injection intertwines a transposition with the transposition of its images. -/
theorem injective_map_swap {X : Type u} {Y : Type v} (j : X → Y)
    (hj : Function.Injective j) (x y c : X) :
    j (Equiv.swap x y c) = Equiv.swap (j x) (j y) (j c) := by
  classical
  by_cases hx : c = x
  · subst c
    simp
  · by_cases hy : c = y
    · subst c
      simp
    · have hx' : j c ≠ j x := fun h => hx (hj h)
      have hy' : j c ≠ j y := fun h => hy (hj h)
      simp [Equiv.swap_apply_def, hx, hy, hx', hy',
        Ne.symm hx, Ne.symm hy, Ne.symm hx', Ne.symm hy']

/-- The two kinds of generators used on Y in the crossing-subset argument. -/
theorem componentMap_edgePerm
    (hreplace : ∀ u v g, D.WalkValue T b u v (i g) → D.WalkValue N a u v g)
    {e : E} (he : e ∈ N ∨ e ∉ T) (c : D.Component N a ha) :
    D.componentMap N T a b ha hb hNT i hi (D.componentEdgePerm N a ha e c) =
      D.componentEdgePerm T b hb e
        (D.componentMap N T a b ha hb hNT i hi c) := by
  classical
  rcases he with he | he
  · rw [D.componentEdgePerm_of_mem N a ha he,
      D.componentEdgePerm_of_mem T b hb (hNT he)]
    change D.componentMap N T a b ha hb hNT i hi
      (D.componentTranslation N a ha (a e) c) =
      D.componentTranslation T b hb (b e)
        (D.componentMap N T a b ha hb hNT i hi c)
    rw [D.componentMap_translation, hi e he]
  · have heN : e ∉ N := fun h => he (hNT h)
    rw [D.componentEdgePerm_of_not_mem N a ha heN,
      D.componentEdgePerm_of_not_mem T b hb he]
    simpa only [D.componentMap_distinguished] using
      (injective_map_swap (D.componentMap N T a b ha hb hNT i hi)
        (D.componentMap_injective N T a b ha hb hNT i hi hreplace)
        (D.component N a ha (D.source e) 1)
        (D.component N a ha (D.target e) 1) c)

/-- Hence each relevant generator preserves Y and its complement. -/
theorem componentMap_range_edgePerm
    (hreplace : ∀ u v g, D.WalkValue T b u v (i g) → D.WalkValue N a u v g)
    {e : E} (he : e ∈ N ∨ e ∉ T) (c : D.Component T b hb) :
    D.componentEdgePerm T b hb e c ∈
        Set.range (D.componentMap N T a b ha hb hNT i hi) ↔
      c ∈ Set.range (D.componentMap N T a b ha hb hNT i hi) := by
  have hpres : ∀ d, d ∈ Set.range (D.componentMap N T a b ha hb hNT i hi) →
      D.componentEdgePerm T b hb e d ∈
        Set.range (D.componentMap N T a b ha hb hNT i hi) := by
    rintro d ⟨x,rfl⟩
    exact ⟨D.componentEdgePerm N a ha e x,
      D.componentMap_edgePerm N T a b ha hb hNT i hi hreplace he x⟩
  constructor
  · intro h
    have h' := hpres _ h
    simpa only [D.componentEdgePerm_involutive T b hb e c] using h'
  · exact hpres c

end EdgeGraph
end GluingEPPA.Steiner
