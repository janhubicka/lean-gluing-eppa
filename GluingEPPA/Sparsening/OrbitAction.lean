import GluingEPPA.Sparsening.OrbitAtlas

/-! The generic affine action now has its canonical instance. All membership
and incidence equivariance, identity and composition are derived from the
actual orbit atlas, not supplied by an application. -/
namespace GluingEPPA.Sparsening.OrbitAtlas
universe u v w
variable {L : Nat → Type u} {A : Type v} {F : Type w}
variable (R : RelStructure L A) (out : F → A → Set A) (root : Set A)

abbrev Edges := CompleteChartGraph.Edge (Chart R out root)
noncomputable def graph : EdgeGraph (Chart R out root) (Edges R out root) :=
  CompleteChartGraph.graph (Chart R out root)

def canonical (h : Aut R out) :
    ChartAtlas.AtlasSymmetry (graph R out root) (support R out root) where
  ambient := h.perm
  charts := chartPerm R out root h
  edges := CompleteChartGraph.perm (chartPerm R out root h)
  mem_iff x s := chartPerm_mem R out root h s x
  inc_iff := CompleteChartGraph.perm_inc (chartPerm R out root h)

private theorem symmetry_ext {V E B : Type*} {G : EdgeGraph V E}
    {supp : B → V → Prop} {D H : ChartAtlas.AtlasSymmetry G supp}
    (ha : D.ambient = H.ambient) (hc : D.charts = H.charts)
    (he : D.edges = H.edges) : D = H := by
  cases D
  cases H
  cases ha
  cases hc
  cases he
  rfl

@[simp] theorem canonical_trans (h g : Aut R out) :
    canonical R out root (h.trans g) =
      (canonical R out root h).trans (canonical R out root g) := by
  apply symmetry_ext
  · rfl
  · exact chartPerm_trans R out root h g
  · change CompleteChartGraph.perm (chartPerm R out root (h.trans g)) =
      (CompleteChartGraph.perm (chartPerm R out root h)).trans
        (CompleteChartGraph.perm (chartPerm R out root g))
    rw [chartPerm_trans, CompleteChartGraph.perm_trans]

section Finite
open scoped Classical
noncomputable section
variable [Finite A]
local instance chartsFintype : Fintype (Chart R out root) := Fintype.ofFinite _
local instance edgesFintype : Fintype (Edges R out root) := Fintype.ofFinite _

abbrev Vertex := ChartAtlas.Vertex (graph R out root) (support R out root)

def relations : RelStructure L (Vertex R out root) :=
  ChartAtlas.quotientStructure (graph R out root) (support R out root) R

def outputs : F → Vertex R out root → Set (Vertex R out root) :=
  ChartAtlas.liftOutput (graph R out root) (support R out root) out (closed R out root)

/-- An actual automorphism of the relational AND unary quotient structure. -/
def lift (h : Aut R out) (delta : Edges R out root → ZMod 2) :
    Aut (relations R out root) (outputs R out root) where
  perm := (canonical R out root h).quotientEquiv delta
  rel_iff r x := (canonical R out root h).map_rel_iff delta R h.rel_iff r x
  unary_iff f x y := by
    let D := canonical R out root h
    change D.map delta y ∈ outputs R out root f (D.map delta x) ↔
      y ∈ outputs R out root f x
    have himg := D.map_output_image out (closed R out root) delta h.unary_iff f x
    change D.map delta '' outputs R out root f x =
      outputs R out root f (D.map delta x) at himg
    rw [← himg]
    constructor
    · rintro ⟨z, hz, heq⟩
      have he : z = y := (D.quotientEquiv delta).injective heq
      exact he ▸ hz
    · intro hy
      exact ⟨y, hy, rfl⟩

@[simp] theorem canonical_refl : canonical R out root Aut.refl =
    ChartAtlas.AtlasSymmetry.identity (G := graph R out root)
      (support := support R out root) := by
  apply symmetry_ext
  · rfl
  · exact chartPerm_refl R out root
  · change CompleteChartGraph.perm (chartPerm R out root Aut.refl) = Equiv.refl _
    rw [chartPerm_refl, CompleteChartGraph.perm_refl]

/-- Composition of canonical lifts, with the actual orbit action downstairs. -/
theorem lift_comp (h g : Aut R out) (delta epsilon : Edges R out root → ZMod 2)
    (q : Vertex R out root) :
    (lift R out root g epsilon).perm ((lift R out root h delta).perm q) =
      (lift R out root (h.trans g)
        (epsilon + coordinateMap (canonical R out root g).edges delta)).perm q := by
  change (canonical R out root g).map epsilon ((canonical R out root h).map delta q) = _
  rw [(canonical R out root h).map_comp, ← canonical_trans]
  rfl

theorem lift_identity (q : Vertex R out root) :
    (lift R out root Aut.refl 0).perm q = q := by
  change (canonical R out root Aut.refl).map 0 q = q
  rw [canonical_refl, ChartAtlas.AtlasSymmetry.identity_map]

instance finite_vertex : Finite (Vertex R out root) := inferInstance
end
end Finite
end GluingEPPA.Sparsening.OrbitAtlas
