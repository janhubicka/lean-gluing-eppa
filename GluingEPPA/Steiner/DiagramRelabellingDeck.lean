import GluingEPPA.Steiner.DiagramRelabellingAction

/-!
# Prefix automorphisms and relabellings on the same free realization

Prefix translations and compatible relabellings commute after
relabelling the prefix word. This is the concrete equation
F_sigma * P_k = P_{alpha_sigma(k)} * F_sigma
required when combining the two symmetries in the coherent EPPA proof.

Also, an involutive valuation element gives an involutive quotient
automorphism. No unproved existence theorem is assumed.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- A compatible relabelling conjugates a prefix translation to
the translation by the relabelled valuation element. -/
theorem relabelPoint_deck (L : LabelledSteiner D Ω)
    (t : LabelledSymmetry D L)
    (k : (family D Finset.univ).Carrier)
    (p : realizedPoint D L) :
    relabelPoint D L t ((realizedDeck D L k) p) =
      (realizedDeck D L (relabelValuation D L t k))
        (relabelPoint D L t p) := by
  induction p using Quotient.inductionOn with
  | _ p =>
      cases p with
      | mk u g x hx =>
          change canonicalPoint D L (t.graph.vertex u)
            (relabelValuation D L t (k * g)) (t.labels x)
              ((t.present u x).2 hx) =
            canonicalPoint D L (t.graph.vertex u)
              (relabelValuation D L t k * relabelValuation D L t g)
              (t.labels x) ((t.present u x).2 hx)
          rw [map_mul]

/-- A valuation involution induces an involution on every point
of the realized Steiner system. -/
theorem realizedDeck_involutive (L : LabelledSteiner D Ω)
    (k : (family D Finset.univ).Carrier) (hk : k * k = 1)
    (p : realizedPoint D L) :
    (realizedDeck D L k) ((realizedDeck D L k) p) = p := by
  change freePointLeft D L (family D Finset.univ).edge
    (fun e => family_square D Finset.univ e) k
    (freePointLeft D L (family D Finset.univ).edge
      (fun e => family_square D Finset.univ e) k p) = p
  rw [freePointLeft_comp, hk, freePointLeft_one]

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
