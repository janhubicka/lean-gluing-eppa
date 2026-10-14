import GluingEPPA.Sparsening.OrbitAction

/-! Endpoint extensions and chart movement for the actual automorphism-orbit
atlas. There is no supplied chart-transitivity or upstairs automorphism
assumption. This is a one-refinement construction, not yet the tree induction. -/
namespace GluingEPPA.Sparsening.OrbitAtlas
universe u v w
variable {L : Nat → Type u} {A : Type v} {F : Type w}
variable (R : RelStructure L A) (out : F → A → Set A) (root : Set A)
open scoped Classical
noncomputable section
variable [Finite A]
local instance chartsFintype : Fintype (Chart R out root) := Fintype.ofFinite _
local instance edgesFintype : Fintype (Edges R out root) := Fintype.ofFinite _

variable (hr : UnaryClosed out (fun x => x ∈ root))

def spokes : ChartAtlas.RootSpokes (graph R out root) (rootChart R out root hr) :=
  ChartAtlas.chooseRootSpokes CompleteChartGraph.complete (rootChart R out root hr)

def endpoint (h : Aut R out) (dom ran : Chart R out root) :
    Aut (relations R out root) (outputs R out root) :=
  lift R out root h (chartTranslation (canonical R out root h).edges
    ((spokes R out root hr).eta dom) ((spokes R out root hr).eta ran))

/-- Every old extension sends the corresponding points of the distinguished
root to the right points upstairs. Domain and range are actual image charts. -/
theorem endpoint_extends (h : Aut R out) (dom : Chart R out root)
    (hdom : dom.val ⊆ root) (hran : h.perm '' dom.val ⊆ root)
    (x : A) (hx : x ∈ dom.val) :
    (endpoint R out root hr h dom (chartPerm R out root h dom)).perm
      (ChartAtlas.copy (graph R out root) (support R out root)
        (rootChart R out root hr) 0 x (hdom hx)) =
      ChartAtlas.copy (graph R out root) (support R out root)
        (rootChart R out root hr) 0 (h.perm x) (hran ⟨x, hx, rfl⟩) := by
  exact (canonical R out root h).root_extension (spokes R out root hr)
    dom (chartPerm R out root h dom) rfl x (hdom hx) hx (hran ⟨x, hx, rfl⟩)

/-- Canonical chart and edge actions compose, so the endpoint cocycle gives
composition for actual relational/unary automorphisms of the refinement. -/
theorem endpoint_comp (h g : Aut R out) (dom mid ran : Chart R out root)
    (q : Vertex R out root) :
    (endpoint R out root hr g mid ran).perm
      ((endpoint R out root hr h dom mid).perm q) =
      (endpoint R out root hr (h.trans g) dom ran).perm q := by
  change (canonical R out root g).map _ ((canonical R out root h).map _ q) = _
  have hh := (canonical R out root h).endpoint_map_comp (canonical R out root g)
    (spokes R out root hr) dom mid ran q
  simpa only [endpoint, lift, ChartAtlas.AtlasSymmetry.quotientEquiv,
    canonical_trans] using hh

theorem endpoint_identity (dom : Chart R out root) (q : Vertex R out root) :
    (endpoint R out root hr Aut.refl dom dom).perm q = q := by
  change (canonical R out root Aut.refl).map _ q = q
  rw [canonical_refl]
  exact ChartAtlas.AtlasSymmetry.endpoint_identity (spokes R out root hr) dom q

def liftedChart (s : Chart R out root) (chi : Edges R out root → ZMod 2) :
    Set (Vertex R out root) :=
  {q | ∃ x hx, ChartAtlas.copy (graph R out root) (support R out root) s chi x hx = q}

/-- Uniformly move a whole smaller chart into any containing chart by one
spoke (or the zero walk), without choosing a different valuation per point. -/
theorem liftedChart_inclusion (s t : Chart R out root) (incl : s.val ⊆ t.val)
    (chi : Edges R out root → ZMod 2) :
    ∃ psi, liftedChart R out root s chi ⊆ liftedChart R out root t psi := by
  obtain ⟨c, _, hc⟩ := exists_spoke (graph R out root) CompleteChartGraph.complete s t
  refine ⟨chi + c, ?_⟩
  rintro q ⟨x, hx, rfl⟩
  refine ⟨x, incl hx, ?_⟩
  exact (ChartAtlas.copy_eq_of_path (graph R out root) (support R out root)
    x hx (incl hx) ((hc (support R out root x) hx (incl hx)).1 chi)).symm

/-- Every actual subchart is contained in some lifted full chart. -/
theorem liftedChart_in_full (s : Chart R out root) (chi : Edges R out root → ZMod 2) :
    ∃ (h : Aut R out) psi,
      liftedChart R out root s chi ⊆ liftedChart R out root (fullChart R out root hr h) psi := by
  obtain ⟨h, hh⟩ := contained_in_full R out root hr s
  obtain ⟨psi, hp⟩ := liftedChart_inclusion R out root s (fullChart R out root hr h) hh chi
  exact ⟨h, psi, hp⟩

theorem fullChart_back (h : Aut R out) :
    chartPerm R out root h.symm (fullChart R out root hr h) = rootChart R out root hr := by
  apply Subtype.ext
  ext x
  change x ∈ h.perm.symm '' (h.perm '' root) ↔ x ∈ root
  simp

/-- Full-chart transitivity is derived from the defining old orbit and the
free translation parameter, rather than inserted as an atlas axiom. -/
theorem fullChart_to_root (h : Aut R out) (chi : Edges R out root → ZMod 2) :
    ∃ a : Aut (relations R out root) (outputs R out root),
      a.perm '' liftedChart R out root (fullChart R out root hr h) chi =
        liftedChart R out root (rootChart R out root hr) 0 := by
  obtain ⟨delta, hh⟩ := (canonical R out root h.symm).exists_translation_chart
    (fullChart R out root hr h) chi 0
  refine ⟨lift R out root h.symm delta, ?_⟩
  change (canonical R out root h.symm).map delta ''
    liftedChart R out root (fullChart R out root hr h) chi = _
  change (canonical R out root h.symm).map delta ''
    liftedChart R out root (fullChart R out root hr h) chi =
    liftedChart R out root (chartPerm R out root h.symm (fullChart R out root hr h)) 0 at hh
  rw [fullChart_back R out root hr h] at hh
  exact hh

/-- The actual automorphic movement required once irreducible containment
has been proved: every lifted chart, not merely every abstract copy, moves
inside the distinguished root by a full relational/unary automorphism. -/
theorem chart_to_root (s : Chart R out root) (chi : Edges R out root → ZMod 2) :
    ∃ a : Aut (relations R out root) (outputs R out root),
      a.perm '' liftedChart R out root s chi ⊆
        liftedChart R out root (rootChart R out root hr) 0 := by
  obtain ⟨h, psi, hi⟩ := liftedChart_in_full R out root hr s chi
  obtain ⟨a, ha⟩ := fullChart_to_root R out root hr h psi
  refine ⟨a, ?_⟩
  rintro q ⟨p, hp, heq⟩
  have hq : q ∈ a.perm '' liftedChart R out root (fullChart R out root hr h) psi :=
    ⟨p, hi hp, heq⟩
  rw [ha] at hq
  exact hq

end
end GluingEPPA.Sparsening.OrbitAtlas
