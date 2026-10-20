import GluingEPPA.Steiner.FiniteTransport
import GluingEPPA.Steiner.LocalTriples

/-!
# Transporting Steiner triples in the finite cover

An edge identifies any label in its domain, and its domain is closed under
Steiner completion. The unconditional finite transport theorem synchronizes
separate carrying walks. The resulting quotient therefore has unique
third-point completion and closed canonical charts.

The relation `liftRel` means a label is carried by *some* lifted walk
between the two chart sites; it does not introduce new identifications.
-/

namespace GluingEPPA.Steiner

universe u v
variable {V E : Type u} {A : Type v}
variable [Fintype E] [DecidableEq E] [Finite V]
attribute [local instance] Classical.propDecidable

structure LabelledGraph (V E : Type u) (A : Type v) where
  graph : EdgeGraph V E
  carries : E → A → Prop
  triple : V → A → A → A → Prop
  triple_unique : ∀ {s x y z z'}, triple s x y z → triple s x y z' → z = z'
  edge_closed : ∀ {e s t x y z}, graph.Joins e s t →
    triple s x y z → carries e x → carries e y →
      carries e z ∧ triple t x y z

namespace LabelledGraph

variable (D : LabelledGraph V E A)

def mask (x : A) : Set E := {e | D.carries e x}

abbrev Sheet := V × FiniteFamily.FullGroup D.graph

/-- Two lifted chart sites carry the same occurrence of label x precisely
when a walk of x-carrying edges has the prescribed group value. -/
def liftRel (x : A) (s t : D.Sheet) : Prop :=
  D.graph.WalkValue (D.mask x) (FiniteFamily.fullEdge D.graph)
    s.1 t.1 (s.2⁻¹ * t.2)

theorem liftRel_refl (x : A) (s : D.Sheet) : D.liftRel x s s := by
  change D.graph.WalkValue (D.mask x) (FiniteFamily.fullEdge D.graph)
    s.1 s.1 (s.2⁻¹ * s.2)
  simpa using (EdgeGraph.WalkValue.nil (D := D.graph) (S := D.mask x)
    (a := FiniteFamily.fullEdge D.graph) s.1)

theorem liftRel_symm (x : A) {s t : D.Sheet} (h : D.liftRel x s t) :
    D.liftRel x t s := by
  change D.graph.WalkValue (D.mask x) (FiniteFamily.fullEdge D.graph)
    s.1 t.1 (s.2⁻¹ * t.2) at h
  have p := EdgeGraph.WalkValue.symm
    (D := D.graph) (S := D.mask x)
    (a := FiniteFamily.fullEdge D.graph)
    (fun e _ => FiniteFamily.fullEdge_involutive D.graph e) h
  have hv : (s.2⁻¹ * t.2)⁻¹ = t.2⁻¹ * s.2 := by group
  simpa only [liftRel, hv] using p

theorem liftRel_trans (x : A) {s t r : D.Sheet}
    (h : D.liftRel x s t) (k : D.liftRel x t r) :
    D.liftRel x s r := by
  have p := EdgeGraph.WalkValue.trans h k
  have hv : (s.2⁻¹ * t.2) * (t.2⁻¹ * r.2) = s.2⁻¹ * r.2 := by group
  simpa only [liftRel, hv] using p

/-- Every walk whose edges carry the first two labels also carries the
entire triple. This is where closedness of edge domains is used. -/
theorem triple_along_walk {u v : V} {g : FiniteFamily.FullGroup D.graph}
    {x y z : A}
    (p : D.graph.WalkValue (D.mask x ∩ D.mask y)
      (FiniteFamily.fullEdge D.graph) u v g) :
    D.triple u x y z →
      D.graph.WalkValue (D.mask z) (FiniteFamily.fullEdge D.graph) u v g ∧
        D.triple v x y z := by
  induction p with
  | nil =>
      intro ht
      exact ⟨.nil _, ht⟩
  | @cons u v w e g he hj p ih =>
      intro ht
      obtain ⟨hz, hv⟩ := D.edge_closed hj ht he.1 he.2
      obtain ⟨pz, hw⟩ := ih hv
      exact ⟨.cons hz hj pz, hw⟩

/-- The actual finite-sheet gluing diagram, with a point step standing for
reachability by a lifted carrying path. -/
noncomputable def lifted : TripleDiagram D.Sheet A where
  step := fun s t x => D.liftRel x s t
  step_symm := by
    intro s t x h
    exact D.liftRel_symm x h
  triple := fun s x y z => D.triple s.1 x y z
  triple_unique := by
    intro s x y z z' h k
    exact D.triple_unique h k
  close_step := by
    intro s t x y z ht hx hy
    have both : D.graph.WalkValue (D.mask x ∩ D.mask y)
        (FiniteFamily.fullEdge D.graph) s.1 t.1 (s.2⁻¹ * t.2) :=
      (FiniteFamily.exactTransport D.graph (D.mask x) (D.mask y)
        s.1 t.1 (s.2⁻¹ * t.2)).mpr ⟨hx, hy⟩
    exact D.triple_along_walk both ht

/-- A carrying path in the lifted diagram is already represented by one
actual carrying walk, since its step relation is reflexive and transitive. -/
theorem carries_as_walk (x : A) {s t : D.Sheet}
    (h : (D.lifted).Carries x s t) : D.liftRel x s t := by
  induction h with
  | refl => exact D.liftRel_refl x _
  | tail _ e ih => exact D.liftRel_trans x ih e

/-- The finite transport theorem synchronizes any two label occurrences. -/
theorem lifted_synchronizes : (D.lifted).Synchronizes := by
  intro s t x y hx hy
  have px := D.carries_as_walk x hx
  have py := D.carries_as_walk y hy
  have p : D.graph.WalkValue (D.mask x ∩ D.mask y)
      (FiniteFamily.fullEdge D.graph) s.1 t.1 (s.2⁻¹ * t.2) :=
    (FiniteFamily.exactTransport D.graph (D.mask x) (D.mask y)
      s.1 t.1 (s.2⁻¹ * t.2)).mpr ⟨px, py⟩
  exact Relation.ReflTransGen.single
    ⟨p.mono Set.inter_subset_left, p.mono Set.inter_subset_right⟩

/-- In the lifted quotient, two triples with the same first two realized
points necessarily have the same third realized point. -/
theorem lifted_triple_unique {b c d e : (D.lifted).Realization}
    (h : (D.lifted).tripleOnRealization b c d)
    (k : (D.lifted).tripleOnRealization b c e) : d = e :=
  (D.lifted).tripleOnRealization_unique D.lifted_synchronizes h k

/-- Every lifted chart is closed for triples meeting it in two points. -/
theorem lifted_chart_closed {s : D.Sheet} {x y : A}
    {d : (D.lifted).Realization}
    (h : (D.lifted).tripleOnRealization
      ((D.lifted).copy s x) ((D.lifted).copy s y) d) :
    ∃ z, (D.lifted).triple s x y z ∧ (D.lifted).copy s z = d :=
  (D.lifted).tripleOnRealization_closed D.lifted_synchronizes h

end LabelledGraph
end GluingEPPA.Steiner
