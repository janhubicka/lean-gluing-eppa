import GluingEPPA.Sparsening.UnaryAtlas
import GluingEPPA.Sparsening.CoherentTranslation
import GluingEPPA.AffineLift

/-!
Affine actions on the actual varying-size chart quotient. Both the ambient
point and its chart move. Incidence and chart membership are the only geometric
input; quotient well-definedness, inverses and composition are proved here.
-/
namespace GluingEPPA.Sparsening.ChartAtlas
universe u v w z
variable {V : Type u} {E : Type v} {A : Type w}
variable (G : GluingEPPA.EdgeGraph V E) (support : A → V → Prop)

structure AtlasSymmetry where
  ambient : A ≃ A
  charts : V ≃ V
  edges : E ≃ E
  mem_iff : ∀ x s, support (ambient x) (charts s) ↔ support x s
  inc_iff : ∀ e s t, G.Inc (edges e) (charts s) (charts t) ↔ G.Inc e s t

namespace AtlasSymmetry
variable {G support} (D : AtlasSymmetry G support)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The inverse translation is transported back along the edge permutation. -/
def inverseShift (delta : E → ZMod 2) : E → ZMod 2 :=
  fun e => -delta (D.edges e)

def symm : AtlasSymmetry G support where
  ambient := D.ambient.symm
  charts := D.charts.symm
  edges := D.edges.symm
  mem_iff x s := by
    have h := D.mem_iff (D.ambient.symm x) (D.charts.symm s)
    simpa using h.symm
  inc_iff e s t := by
    have h := D.inc_iff (D.edges.symm e) (D.charts.symm s) (D.charts.symm t)
    simpa using h.symm

def occurrenceMap (delta : E → ZMod 2) (x : A)
    (p : Occurrence (E := E) support x) :
    Occurrence (E := E) support (D.ambient x) :=
  ⟨(D.charts p.val.1, EdgeGraph.affine D.edges delta p.val.2),
    (D.mem_iff x p.val.1).mpr p.property⟩

theorem step_map (delta : E → ZMod 2) {x : A}
    {p q : V × (E → ZMod 2)} (h : restrictedLift G (support x) p q) :
    restrictedLift G (support (D.ambient x))
      (D.charts p.1, EdgeGraph.affine D.edges delta p.2)
      (D.charts q.1, EdgeGraph.affine D.edges delta q.2) := by
  obtain ⟨⟨e, he, hq⟩, hp, ht⟩ := h
  refine ⟨⟨D.edges e, (D.inc_iff e p.1 q.1).mpr he, ?_⟩,
    (D.mem_iff x p.1).mpr hp, (D.mem_iff x q.1).mpr ht⟩
  rw [hq, EdgeGraph.affine_flip]

theorem path_map (delta : E → ZMod 2) {x : A}
    {p q : V × (E → ZMod 2)}
    (h : Relation.ReflTransGen (restrictedLift G (support x)) p q) :
    Relation.ReflTransGen (restrictedLift G (support (D.ambient x)))
      (D.charts p.1, EdgeGraph.affine D.edges delta p.2)
      (D.charts q.1, EdgeGraph.affine D.edges delta q.2) := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (D.step_map delta e)

def pointMap (delta : E → ZMod 2) (x : A) :
    Quotient (pointSetoid G support x) →
      Quotient (pointSetoid G support (D.ambient x)) :=
  Quotient.map (D.occurrenceMap delta x) (fun _ _ h => D.path_map delta h)

def map (delta : E → ZMod 2) (q : Vertex G support) : Vertex G support :=
  ⟨D.ambient q.1, D.pointMap delta q.1 q.2⟩

@[simp] theorem map_copy (delta chi : E → ZMod 2) (s : V) (x : A)
    (hx : support x s) :
    D.map delta (copy G support s chi x hx) =
      copy G support (D.charts s) (EdgeGraph.affine D.edges delta chi)
        (D.ambient x) ((D.mem_iff x s).mpr hx) := rfl

@[simp] theorem project_map (delta : E → ZMod 2) (q : Vertex G support) :
    project G support (D.map delta q) = D.ambient (project G support q) := rfl

lemma affine_inverse_left (delta chi : E → ZMod 2) :
    EdgeGraph.affine D.edges.symm (D.inverseShift delta)
      (EdgeGraph.affine D.edges delta chi) = chi := by
  funext e
  simp [EdgeGraph.affine, inverseShift]

lemma affine_inverse_right (delta chi : E → ZMod 2) :
    EdgeGraph.affine D.edges delta
      (EdgeGraph.affine D.edges.symm (D.inverseShift delta) chi) = chi := by
  funext e
  simp [EdgeGraph.affine, inverseShift]

@[simp] theorem symm_map_map (delta : E → ZMod 2) (q : Vertex G support) :
    D.symm.map (D.inverseShift delta) (D.map delta q) = q := by
  obtain ⟨s, chi, hx, hq⟩ := exists_representative G support q
  have h : D.symm.map (D.inverseShift delta)
      (D.map delta (copy G support s chi (project G support q) hx)) =
      copy G support s chi (project G support q) hx := by
    rw [map_copy, map_copy]
    simp only [symm, Equiv.symm_apply_apply, affine_inverse_left]
  simpa only [hq] using h

@[simp] theorem map_symm_map (delta : E → ZMod 2) (q : Vertex G support) :
    D.map delta (D.symm.map (D.inverseShift delta) q) = q := by
  obtain ⟨s, chi, hx, hq⟩ := exists_representative G support q
  have h : D.map delta (D.symm.map (D.inverseShift delta)
      (copy G support s chi (project G support q) hx)) =
      copy G support s chi (project G support q) hx := by
    rw [map_copy, map_copy]
    simp only [symm, Equiv.apply_symm_apply, affine_inverse_right]
  simpa only [hq] using h

def quotientEquiv (delta : E → ZMod 2) : Vertex G support ≃ Vertex G support where
  toFun := D.map delta
  invFun := D.symm.map (D.inverseShift delta)
  left_inv := D.symm_map_map delta
  right_inv := D.map_symm_map delta

def trans (H : AtlasSymmetry G support) : AtlasSymmetry G support where
  ambient := D.ambient.trans H.ambient
  charts := D.charts.trans H.charts
  edges := D.edges.trans H.edges
  mem_iff x s := (H.mem_iff (D.ambient x) (D.charts s)).trans (D.mem_iff x s)
  inc_iff e s t :=
    (H.inc_iff (D.edges e) (D.charts s) (D.charts t)).trans (D.inc_iff e s t)

lemma affine_comp (H : AtlasSymmetry G support) (delta epsilon chi : E → ZMod 2) :
    EdgeGraph.affine H.edges epsilon (EdgeGraph.affine D.edges delta chi) =
      EdgeGraph.affine (D.edges.trans H.edges)
        (epsilon + coordinateMap H.edges delta) chi := by
  funext e
  simp only [EdgeGraph.affine, coordinateMap, Equiv.symm_trans_apply, Pi.add_apply]
  abel

/-- Composition is established on the quotient itself, not just on vectors. -/
theorem map_comp (H : AtlasSymmetry G support) (delta epsilon : E → ZMod 2)
    (q : Vertex G support) :
    H.map epsilon (D.map delta q) =
      (D.trans H).map (epsilon + coordinateMap H.edges delta) q := by
  obtain ⟨s, chi, hx, hq⟩ := exists_representative G support q
  have h : H.map epsilon (D.map delta (copy G support s chi (project G support q) hx)) =
      (D.trans H).map (epsilon + coordinateMap H.edges delta)
        (copy G support s chi (project G support q) hx) := by
    rw [map_copy, map_copy, map_copy, D.affine_comp H]
    rfl
  simpa only [hq] using h

variable {L : Nat → Type z}

def PreservesRelations (R : RelStructure L A) : Prop :=
  ∀ {n} (r : L n) (x : Fin n → A),
    R.rel r (fun i => D.ambient (x i)) ↔ R.rel r x

theorem preservesRelations_symm (R : RelStructure L A) (h : D.PreservesRelations R) :
    D.symm.PreservesRelations R := by
  intro n r x
  simpa only [symm, Equiv.apply_symm_apply] using
    (h r (fun i => D.ambient.symm (x i))).symm

theorem map_rel (delta : E → ZMod 2) (R : RelStructure L A)
    (h : D.PreservesRelations R) {n} (r : L n) (q : Fin n → Vertex G support)
    (hr : (quotientStructure G support R).rel r q) :
    (quotientStructure G support R).rel r (fun i => D.map delta (q i)) := by
  obtain ⟨s, chi, x, hx, heq⟩ := hr
  refine ⟨D.charts s, EdgeGraph.affine D.edges delta chi,
    fun i => ⟨D.ambient (x i).val, (D.mem_iff (x i).val s).mpr (x i).property⟩,
    (h r (fun i => (x i).val)).mpr hx, ?_⟩
  intro i
  exact congrArg (D.map delta) (heq i)

theorem map_rel_iff (delta : E → ZMod 2) (R : RelStructure L A)
    (h : D.PreservesRelations R) {n} (r : L n) (q : Fin n → Vertex G support) :
    (quotientStructure G support R).rel r (fun i => D.map delta (q i)) ↔
      (quotientStructure G support R).rel r q := by
  constructor
  · intro hr
    have hh := D.symm.map_rel (D.inverseShift delta) R
      (D.preservesRelations_symm R h) r (fun i => D.map delta (q i)) hr
    simpa only [symm_map_map] using hh
  · exact D.map_rel delta R h r q

end AtlasSymmetry
end GluingEPPA.Sparsening.ChartAtlas
