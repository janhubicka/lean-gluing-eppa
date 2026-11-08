import GluingEPPA.Steiner.DiagramRelabellingEquiv

/-!
# Identity and composition of compatible gluing-diagram relabellings

A relabelling includes the base-graph isomorphism, the point-label
permutation, and preservation of all local Steiner triples and gluing
overlaps. Composition is coordinatewise. The associated isomorphisms
of the actual recursively constructed valuation family compose exactly.
This is a prerequisite for the coherent EPPA extension formula.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

namespace LabelledSymmetry

/-- The identity preserves every local system and overlap. -/
def id (L : LabelledSteiner D Ω) : LabelledSymmetry D L where
  graph := Iso.refl D
  labels := Equiv.refl Ω
  present := fun _ _ => Iff.rfl
  triple := fun _ _ _ _ => Iff.rfl
  overlap := fun _ _ => Iff.rfl

/-- First relabel by t, then by s. -/
def trans (L : LabelledSteiner D Ω)
    (t s : LabelledSymmetry D L) : LabelledSymmetry D L where
  graph := t.graph.trans s.graph
  labels := t.labels.trans s.labels
  present := fun u x =>
    (s.present (t.graph.vertex u) (t.labels x)).trans (t.present u x)
  triple := fun u x y z =>
    (s.triple (t.graph.vertex u) (t.labels x) (t.labels y)
      (t.labels z)).trans (t.triple u x y z)
  overlap := fun e x =>
    (s.overlap (t.graph.edge e) (t.labels x)).trans (t.overlap e x)

end LabelledSymmetry

/-- The identity relabelling acts identically on the actual valuation group. -/
theorem relabelValuation_id (L : LabelledSteiner D Ω) :
    relabelValuation D L (LabelledSymmetry.id D L) =
      MulEquiv.refl (family D Finset.univ).Carrier := by
  exact naturalIso_refl D Finset.univ

/-- The valuation isomorphism of a composite relabelling is the
composite of the two existing valuation isomorphisms. -/
theorem relabelValuation_trans (L : LabelledSteiner D Ω)
    (t s : LabelledSymmetry D L) :
    relabelValuation D L (LabelledSymmetry.trans D L t s) =
      (relabelValuation D L t).trans (relabelValuation D L s) := by
  exact (naturalIso_comp D D D t.graph s.graph
    Finset.univ Finset.univ Finset.univ
    (by intro e; simp) (by intro e; simp)).symm

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
