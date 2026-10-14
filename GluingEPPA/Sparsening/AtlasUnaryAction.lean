import GluingEPPA.Sparsening.AtlasAction

/-! Affine quotient actions preserve entire unary output sets. The old map
is a bijection preserving and reflecting unary incidence, so no graph-only
homomorphism assumption replaces equality of the lifted full fibres. -/
namespace GluingEPPA.Sparsening.ChartAtlas.AtlasSymmetry
universe u v w z
variable {V : Type u} {E : Type v} {A : Type w} {F : Type z}
variable {G : GluingEPPA.EdgeGraph V E} {support : A → V → Prop}
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (D : AtlasSymmetry G support)

def PreservesUnary (out : F → A → Set A) : Prop :=
  ∀ f x y, D.ambient y ∈ out f (D.ambient x) ↔ y ∈ out f x

theorem preservesUnary_symm (out : F → A → Set A) (h : D.PreservesUnary out) :
    D.symm.PreservesUnary out := by
  intro f x y
  simpa only [symm, Equiv.apply_symm_apply] using
    (h f (D.ambient.symm x) (D.ambient.symm y)).symm

variable (out : F → A → Set A)
variable (closed : ∀ f x y s, support x s → y ∈ out f x → support y s)

lemma map_output_mem_copy (delta : E → ZMod 2) (h : D.PreservesUnary out)
    (f : F) (s : V) (chi : E → ZMod 2) (x : A) (hx : support x s)
    (z : Vertex G support)
    (hz : z ∈ liftOutput G support out closed f (copy G support s chi x hx)) :
    D.map delta z ∈ liftOutput G support out closed f
      (D.map delta (copy G support s chi x hx)) := by
  obtain ⟨y, hy, rfl⟩ := (liftOutput_copy G support out closed f s chi x hx z).mp hz
  rw [map_copy, map_copy]
  apply (liftOutput_copy G support out closed f (D.charts s)
    (EdgeGraph.affine D.edges delta chi) (D.ambient x)
    ((D.mem_iff x s).mpr hx) _).mpr
  exact ⟨D.ambient y, (h f x y).mpr hy, rfl⟩

theorem map_output_mem (delta : E → ZMod 2) (h : D.PreservesUnary out)
    (f : F) (q z : Vertex G support)
    (hz : z ∈ liftOutput G support out closed f q) :
    D.map delta z ∈ liftOutput G support out closed f (D.map delta q) := by
  obtain ⟨s, chi, hx, hq⟩ := exists_representative G support q
  have hz' : z ∈ liftOutput G support out closed f
      (copy G support s chi (project G support q) hx) := by
    simpa only [hq] using hz
  have hh := D.map_output_mem_copy out closed delta h f s chi
    (project G support q) hx z hz'
  simpa only [hq] using hh

/-- The action maps each full unary fibre ONTO its target fibre. -/
theorem map_output_image (delta : E → ZMod 2) (h : D.PreservesUnary out)
    (f : F) (q : Vertex G support) :
    D.map delta '' liftOutput G support out closed f q =
      liftOutput G support out closed f (D.map delta q) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact D.map_output_mem out closed delta h f q y hy
  · intro hz
    refine ⟨D.symm.map (D.inverseShift delta) z, ?_, D.map_symm_map delta z⟩
    have hh := D.symm.map_output_mem out closed (D.inverseShift delta)
      (D.preservesUnary_symm out h) f (D.map delta q) z hz
    simpa only [symm_map_map] using hh

end GluingEPPA.Sparsening.ChartAtlas.AtlasSymmetry
