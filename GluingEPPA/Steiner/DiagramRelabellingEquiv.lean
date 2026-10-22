import GluingEPPA.Steiner.DiagramRelabelling

/-!
# Relabellings are bijections on the free quotient

A compatible relabelling of the base graph and local systems induces
a bijection of quotient points. Injectivity uses the *reverse*
direction of the already checked Cayley-walk naturality theorem;
surjectivity chooses inverse base, valuation and point-label
coordinates. No assumed EPPA witness or graph-only symmetry is used.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- The quotient relabelling is injective, since it preserves and
reflects the exact point-identification relation. -/
theorem relabelPoint_injective (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L) :
    Function.Injective (relabelPoint D L t) := by
  intro p q hpq
  induction p using Quotient.inductionOn with
  | _ p =>
    induction q using Quotient.inductionOn with
    | _ q =>
      apply Quotient.sound
      have hh : (pointSetoid D L (family D Finset.univ).edge
          (fun e => family_square D Finset.univ e)).r
          (relabelOccurrence D L t p) (relabelOccurrence D L t q) := by
        exact Quotient.exact hpq
      change t.labels p.label = t.labels q.label ∧
        D.CayleyWalk (edgesCarrying L.overlap (t.labels p.label))
          (family D Finset.univ).edge
          (t.graph.vertex p.site) (relabelValuation D L t p.sheet)
          (t.graph.vertex q.site) (relabelValuation D L t q.sheet) at hh
      change p.label = q.label ∧
        D.CayleyWalk (edgesCarrying L.overlap p.label)
          (family D Finset.univ).edge
          p.site p.sheet q.site q.sheet
      refine ⟨t.labels.injective hh.1, ?_⟩
      exact (Iso.cayleyWalk_iff t.graph
        (edgesCarrying L.overlap p.label)
        (edgesCarrying L.overlap (t.labels p.label))
        (family D Finset.univ).edge (family D Finset.univ).edge
        (relabelValuation D L t)
        (by intro e; exact t.overlap e p.label)
        (by
          intro e _
          exact naturalIso_all_edges D D t.graph Finset.univ Finset.univ
            (by intro f; simp) e)
        p.site q.site p.sheet q.sheet).mp hh.2

/-- Every quotient point has a preimage, using the three inverse
    coordinate bijections. -/
theorem relabelPoint_surjective (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L) :
    Function.Surjective (relabelPoint D L t) := by
  intro p
  induction p using Quotient.inductionOn with
  | _ p =>
    cases p with
    | mk u g x hx =>
      have hpre : L.present (t.graph.vertex.symm u) (t.labels.symm x) := by
        apply (t.present (t.graph.vertex.symm u) (t.labels.symm x)).1
        simpa using hx
      refine ⟨canonicalPoint D L (t.graph.vertex.symm u)
        (relabelValuation D L t).symm g (t.labels.symm x) hpre, ?_⟩
      rw [relabelPoint_canonical]
      simp

/-- The compatible relabelling induces an actual permutation, not
    merely a triple-preserving endomap. -/
noncomputable def relabelPointEquiv (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L) : Equiv.Perm (realizedPoint D L) :=
  Equiv.ofBijective (relabelPoint D L t)
    ⟨relabelPoint_injective D L t, relabelPoint_surjective D L t⟩

/-- The resulting permutation preserves the quotient Steiner triples. -/
theorem relabelPointEquiv_preserves_triple (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L)
    (p q r : realizedPoint D L)
    (h : realizedTriple D L p q r) :
    realizedTriple D L (relabelPointEquiv D L t p)
      (relabelPointEquiv D L t q) (relabelPointEquiv D L t r) :=
  relabelPoint_preserves_triple D L t p q r h

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
