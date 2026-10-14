import GluingEPPA.Sparsening.AtlasUnaryAction

/-!
Endpoint translations give actual extensions on the chart quotient. Rooted
spokes include the zero path at the root and are chosen once, uniformly in
point supports. Composition is proved for the quotient maps themselves.
-/
namespace GluingEPPA.Sparsening.ChartAtlas
universe u v w
variable {V : Type u} {E : Type v} {A : Type w}
variable {G : GluingEPPA.EdgeGraph V E} {support : A → V → Prop}
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

structure RootSpokes (G : GluingEPPA.EdgeGraph V E) (root : V) where
  eta : V → E → ZMod 2
  root_zero : eta root = 0
  walks : ∀ t (K : V → Prop), K root → K t →
    Realizes G K root t (eta t) ∧ Realizes G K t root (eta t)

noncomputable def chooseRootSpokes
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b) (root : V) :
    RootSpokes G root := by
  classical
  choose eta he hw using (fun t => exists_spoke G complete root t)
  exact ⟨eta, he root rfl, hw⟩

namespace AtlasSymmetry
variable (D : AtlasSymmetry G support)

lemma affine_zero (delta : E → ZMod 2) :
    EdgeGraph.affine D.edges delta 0 = delta := by
  funext e
  simp [EdgeGraph.affine]

lemma affine_endpoint (etaD etaR : E → ZMod 2) :
    EdgeGraph.affine D.edges (chartTranslation D.edges etaD etaR) etaD = etaR := by
  funext e
  change etaD (D.edges.symm e) + (etaR e + etaD (D.edges.symm e)) = etaR e
  calc
    etaD (D.edges.symm e) + (etaR e + etaD (D.edges.symm e)) =
      etaR e + (etaD (D.edges.symm e) + etaD (D.edges.symm e)) := by abel
    _ = etaR e := by rw [bit_add_self, add_zero]

/-- Both repeated-endpoint and empty-domain cases are permitted. For any
point of the domain, the two spokes carry its image to the distinguished copy. -/
theorem root_extension {root : V} (spokes : RootSpokes G root)
    (dom ran : V) (hdom : D.charts dom = ran) (x : A)
    (hxroot : support x root) (hxdom : support x dom)
    (hyroot : support (D.ambient x) root) :
    D.map (chartTranslation D.edges (spokes.eta dom) (spokes.eta ran))
      (copy G support root 0 x hxroot) =
      copy G support root 0 (D.ambient x) hyroot := by
  have hstart : Relation.ReflTransGen (restrictedLift G (support x))
      (root, 0) (dom, spokes.eta dom) := by
    simpa only [zero_add] using (spokes.walks dom (support x) hxroot hxdom).1 0
  have hyran : support (D.ambient x) ran :=
    hdom ▸ (D.mem_iff x dom).mpr hxdom
  let delta := chartTranslation D.edges (spokes.eta dom) (spokes.eta ran)
  have hfirst : Relation.ReflTransGen (restrictedLift G (support (D.ambient x)))
      (D.charts root, delta) (ran, spokes.eta ran) := by
    simpa only [delta, D.affine_zero, D.affine_endpoint, hdom] using D.path_map delta hstart
  have hlast : Relation.ReflTransGen (restrictedLift G (support (D.ambient x)))
      (ran, spokes.eta ran) (root, 0) := by
    simpa only [vector_add_self] using
      (spokes.walks ran (support (D.ambient x)) hyroot hyran).2 (spokes.eta ran)
  rw [map_copy, D.affine_zero]
  exact copy_eq_of_path G support (D.ambient x)
    ((D.mem_iff x root).mpr hxroot) hyroot (hfirst.trans hlast)

/-- Endpoint cochain cancellation is lifted to equality of actual quotient maps. -/
theorem endpoint_map_comp (H : AtlasSymmetry G support) {root : V}
    (spokes : RootSpokes G root) (dom mid ran : V) (q : Vertex G support) :
    H.map (chartTranslation H.edges (spokes.eta mid) (spokes.eta ran))
      (D.map (chartTranslation D.edges (spokes.eta dom) (spokes.eta mid)) q) =
    (D.trans H).map (chartTranslation (D.edges.trans H.edges)
      (spokes.eta dom) (spokes.eta ran)) q := by
  rw [D.map_comp H, chartTranslation_comp]

def identity : AtlasSymmetry G support where
  ambient := Equiv.refl A
  charts := Equiv.refl V
  edges := Equiv.refl E
  mem_iff _ _ := Iff.rfl
  inc_iff _ _ _ := Iff.rfl

@[simp] theorem identity_map (q : Vertex G support) :
    (identity (G := G) (support := support)).map 0 q = q := by
  obtain ⟨s, chi, hx, hq⟩ := exists_representative G support q
  have h : (identity (G := G) (support := support)).map 0
      (copy G support s chi (project G support q) hx) =
      copy G support s chi (project G support q) hx := by
    rw [map_copy]
    simp [identity, EdgeGraph.affine]
  simpa only [hq] using h

theorem endpoint_identity {root : V} (spokes : RootSpokes G root)
    (dom : V) (q : Vertex G support) :
    (identity (G := G) (support := support)).map
      (chartTranslation (Equiv.refl E) (spokes.eta dom) (spokes.eta dom)) q = q := by
  rw [chartTranslation_identity, identity_map]

/-- The image of a whole lifted chart is exactly its affine-transformed chart. -/
theorem map_chart_image (delta chi : E → ZMod 2) (s : V) :
    D.map delta '' {q | ∃ x hx, copy G support s chi x hx = q} =
      {q | ∃ x hx, copy G support (D.charts s)
        (EdgeGraph.affine D.edges delta chi) x hx = q} := by
  ext q
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨D.ambient x, (D.mem_iff x s).mpr hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hx : support (D.ambient.symm y) s := by
      apply (D.mem_iff (D.ambient.symm y) s).mp
      simpa only [Equiv.apply_symm_apply] using hy
    refine ⟨copy G support s chi (D.ambient.symm y) hx,
      ⟨D.ambient.symm y, hx, rfl⟩, ?_⟩
    rw [map_copy]
    simp only [Equiv.apply_symm_apply]

/-- Any pair of valuations can be matched; base chart transitivity is the
only remaining orbit hypothesis for transitivity on lifted full charts. -/
theorem exists_translation_chart (s : V) (chi psi : E → ZMod 2) :
    ∃ delta : E → ZMod 2,
      D.map delta '' {q | ∃ x hx, copy G support s chi x hx = q} =
        {q | ∃ x hx, copy G support (D.charts s) psi x hx = q} := by
  let delta : E → ZMod 2 := fun e => psi e - chi (D.edges.symm e)
  have h : EdgeGraph.affine D.edges delta chi = psi := by
    funext e
    change chi (D.edges.symm e) + (psi e - chi (D.edges.symm e)) = psi e
    abel
  refine ⟨delta, ?_⟩
  simpa only [h] using D.map_chart_image delta chi s

end AtlasSymmetry
end GluingEPPA.Sparsening.ChartAtlas
