import GluingEPPA.Steiner.DiagramRelabellingDeck

/-!
# The relabelling action on the free Steiner realization

The chosen valuation isomorphisms satisfy identity and composition.
The corresponding quotient maps therefore do so as well. This is
the composition law of the F_sigma maps used in the final coherent
EPPA extension; it is independent of the later construction of
the concrete relabelled-closed-subsystem diagram.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- The identity relabelling fixes every point of the quotient. -/
theorem relabelPoint_id (L : LabelledSteiner D Ω) (p : realizedPoint D L) :
    relabelPoint D L (LabelledSymmetry.id D L) p = p := by
  induction p using Quotient.inductionOn with
  | _ p =>
      cases p with
      | mk u g x hx =>
          change relabelPoint D L (LabelledSymmetry.id D L)
            (canonicalPoint D L u g x hx) =
              canonicalPoint D L u g x hx
          rw [relabelPoint_canonical]
          have hval : relabelValuation D L (LabelledSymmetry.id D L) g = g := by
            have h := congrArg
              (fun F : (family D Finset.univ).Carrier ≃*
                (family D Finset.univ).Carrier => F g)
              (relabelValuation_id D L)
            simpa using h
          change canonicalPoint D L u
            (relabelValuation D L (LabelledSymmetry.id D L) g) x _ =
              canonicalPoint D L u g x hx
          rw [hval]

/-- Relabelling first by t and then by s agrees with the composite
relabelling on every quotient point. -/
theorem relabelPoint_trans (L : LabelledSteiner D Ω)
    (t s : LabelledSymmetry D L) (p : realizedPoint D L) :
    relabelPoint D L (LabelledSymmetry.trans D L t s) p =
      relabelPoint D L s (relabelPoint D L t p) := by
  induction p using Quotient.inductionOn with
  | _ p =>
      cases p with
      | mk u g x hx =>
          change relabelPoint D L (LabelledSymmetry.trans D L t s)
            (canonicalPoint D L u g x hx) =
            relabelPoint D L s
              (relabelPoint D L t (canonicalPoint D L u g x hx))
          rw [relabelPoint_canonical]
          rw [relabelPoint_canonical]
          rw [relabelPoint_canonical]
          have hval : relabelValuation D L (LabelledSymmetry.trans D L t s) g =
              relabelValuation D L s (relabelValuation D L t g) := by
            have h := congrArg
              (fun F : (family D Finset.univ).Carrier ≃*
                (family D Finset.univ).Carrier => F g)
              (relabelValuation_trans D L t s)
            exact h
          change canonicalPoint D L (s.graph.vertex (t.graph.vertex u))
            (relabelValuation D L (LabelledSymmetry.trans D L t s) g)
            (s.labels (t.labels x)) _ =
              canonicalPoint D L (s.graph.vertex (t.graph.vertex u))
              (relabelValuation D L s (relabelValuation D L t g))
              (s.labels (t.labels x)) _
          rw [hval]

/-- Identity in the permutation action on the finite witness. -/
theorem relabelPointEquiv_id (L : LabelledSteiner D Ω) :
    relabelPointEquiv D L (LabelledSymmetry.id D L) =
      Equiv.refl (realizedPoint D L) := by
  apply Equiv.ext
  intro p
  exact relabelPoint_id D L p

/-- Composition in the permutation action on the finite witness. -/
theorem relabelPointEquiv_trans (L : LabelledSteiner D Ω)
    (t s : LabelledSymmetry D L) :
    relabelPointEquiv D L (LabelledSymmetry.trans D L t s) =
      (relabelPointEquiv D L t).trans (relabelPointEquiv D L s) := by
  apply Equiv.ext
  intro p
  exact relabelPoint_trans D L t s p

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
