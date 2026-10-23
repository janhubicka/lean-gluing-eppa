import GluingEPPA.Steiner.DiagramDeck

/-!
# Relabellings of the labelled Steiner gluing diagram

An isomorphism of the underlying edge graph is not sufficient: the
relabelling must also preserve the local point sets, local Steiner
triples and the prescribed closed overlaps. Under these hypotheses
the already checked naturality of the recursive valuation groups maps
actual lifted walks to actual lifted walks. Thus the relabelling
descends to the free quotient and preserves its triples.

This module isolates exactly the additional data needed for the
relabelled-closed-subsystem diagram in the coherent EPPA proof.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- A graph relabelling together with compatible relabellings of local
Steiner systems and gluing overlaps. -/
structure LabelledSymmetry (L : LabelledSteiner D Ω) where
  graph : Iso D D
  labels : Ω ≃ Ω
  present : ∀ u x, L.present (graph.vertex u) (labels x) ↔ L.present u x
  triple : ∀ u x y z,
    L.triple (graph.vertex u) (labels x) (labels y) (labels z) ↔
      L.triple u x y z
  overlap : ∀ e x,
    labels x ∈ L.overlap (graph.edge e) ↔ x ∈ L.overlap e

/-- The actual recursive valuation-group relabelling. -/
noncomputable def relabelValuation (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L) :
    (family D Finset.univ).Carrier ≃* (family D Finset.univ).Carrier :=
  naturalIso D D t.graph Finset.univ Finset.univ (by intro e; simp)

/-- Apply the same relabelling to base vertex, valuation and point label. -/
noncomputable def relabelOccurrence (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L)
    (p : PointOccurrence D L (family D Finset.univ).Carrier) :
    PointOccurrence D L (family D Finset.univ).Carrier :=
  ⟨t.graph.vertex p.site, relabelValuation D L t p.sheet,
    t.labels p.label, (t.present p.site p.label).2 p.valid⟩

/-- Relabellings respect exact transport, including the two lifted endpoints. -/
theorem relabelOccurrence_respects (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L)
    {p q : PointOccurrence D L (family D Finset.univ).Carrier}
    (h : (pointSetoid D L (family D Finset.univ).edge
      (fun e => family_square D Finset.univ e)).r p q) :
    (pointSetoid D L (family D Finset.univ).edge
      (fun e => family_square D Finset.univ e)).r
        (relabelOccurrence D L t p) (relabelOccurrence D L t q) := by
  change p.label = q.label ∧
    D.CayleyWalk (edgesCarrying L.overlap p.label)
      (family D Finset.univ).edge p.site p.sheet q.site q.sheet at h
  change t.labels p.label = t.labels q.label ∧
    D.CayleyWalk (edgesCarrying L.overlap (t.labels p.label))
      (family D Finset.univ).edge
      (t.graph.vertex p.site) (relabelValuation D L t p.sheet)
      (t.graph.vertex q.site) (relabelValuation D L t q.sheet)
  refine ⟨congrArg t.labels h.1, ?_⟩
  exact Iso.map_cayleyWalk t.graph
    (edgesCarrying L.overlap p.label)
    (edgesCarrying L.overlap (t.labels p.label))
    (family D Finset.univ).edge (family D Finset.univ).edge
    (relabelValuation D L t)
    (by intro e; exact t.overlap e p.label)
    (by
      intro e _
      exact naturalIso_all_edges D D t.graph Finset.univ Finset.univ
        (by intro f; simp) e)
    h.2

/-- Every compatible relabelling defines a map on the free quotient. -/
noncomputable def relabelPoint (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L) :
    realizedPoint D L → realizedPoint D L :=
  Quotient.map (relabelOccurrence D L t)
    (fun _ _ h => relabelOccurrence_respects D L t h)

@[simp] theorem relabelPoint_canonical (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L)
    (u : V) (g : (family D Finset.univ).Carrier)
    (x : Ω) (hx : L.present u x) :
    relabelPoint D L t (canonicalPoint D L u g x hx) =
      canonicalPoint D L (t.graph.vertex u)
        (relabelValuation D L t g) (t.labels x)
        ((t.present u x).2 hx) := rfl

/-- The quotient map preserves triples, not only its point labels. -/
theorem relabelPoint_preserves_triple (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L)
    (p q r : realizedPoint D L)
    (ht : realizedTriple D L p q r) :
    realizedTriple D L (relabelPoint D L t p)
      (relabelPoint D L t q) (relabelPoint D L t r) := by
  rcases ht with ⟨u,g,x,y,z,htr,hp,hq,hr⟩
  have htr' : L.triple (t.graph.vertex u)
      (t.labels x) (t.labels y) (t.labels z) :=
    (t.triple u x y z).2 htr
  refine ⟨t.graph.vertex u, relabelValuation D L t g,
    t.labels x, t.labels y, t.labels z, htr', ?_, ?_, ?_⟩
  · rw [hp]
    rfl
  · rw [hq]
    rfl
  · rw [hr]
    rfl

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
