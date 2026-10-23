import GluingEPPA.Steiner.DiagramCoherentFamily

/-!
# The finite Steiner witness and its canonical closed embedding

This module packages the structural part of the *concrete* free
realization: the root copy is injected, its triples are exactly the
input triples, its image is closed, and the quotient is finite.
It also verifies that every chosen coherent extension preserves
Steiner triples.

The separate uniform extension-on-points theorem is the last
ingredient needed for the final EPPA-witness statement.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord
attribute [local instance] Classical.propDecidable

universe u
variable {A : Type u} [Fintype A] [LinearOrder A] [DecidableEq A]
variable (P : Input A)
variable [Fintype (Edge P.triple)] [DecidableEq (Edge P.triple)]

/-- Embed the original labelled input system at the root of the
free realization, with identity valuation. -/
noncomputable def rootEmbedding (x : A) :
    realizedPoint (graph P.triple) (localDiagram P) :=
  canonicalPoint (graph P.triple) (localDiagram P)
    (root P.triple) 1 x (root_present P x)

/-- Point labels cannot collapse under any gluing walk. -/
theorem rootEmbedding_injective : Function.Injective (rootEmbedding P) := by
  intro x y h
  exact canonicalPoint_eq_label (graph P.triple) (localDiagram P)
    (root P.triple) (root P.triple) 1 1 x y
    (root_present P x) (root_present P y) h

/-- Each induced triple in the root embedding is precisely an input
triple; the free quotient creates no additional triples there. -/
theorem rootEmbedding_triple_iff (x y z : A) :
    realizedTriple (graph P.triple) (localDiagram P)
      (rootEmbedding P x) (rootEmbedding P y) (rootEmbedding P z) ↔
      P.triple x y z := by
  exact (canonicalPoint_triple_iff (graph P.triple) (localDiagram P)
    (root P.triple) 1 x y z
    (root_present P x) (root_present P y) (root_present P z)).trans
      (root_triple P.triple x y z)

/-- The root copy is closed: a quotient triple meeting it in two
points has its entire triple represented inside the root. -/
theorem rootEmbedding_closed (x y : A)
    (b : realizedPoint (graph P.triple) (localDiagram P))
    (h : realizedTriple (graph P.triple) (localDiagram P)
      (rootEmbedding P x) (rootEmbedding P y) b) :
    ∃ z : A, P.triple x y z ∧ b = rootEmbedding P z := by
  obtain ⟨z,hz,heq⟩ :=
    realizedTriple_closed (graph P.triple) (localDiagram P)
      (root P.triple) 1 x y (root_present P x) (root_present P y)
      b h
  exact ⟨z,(root_triple P.triple x y z).mp hz,heq⟩

/-- The realized witness is finite. -/
noncomputable instance rootWitness_finite :
    Finite (realizedPoint (graph P.triple) (localDiagram P)) := by
  infer_instance

/-- All chosen coherent maps preserve the partial Steiner triples
of the *actual* quotient, not merely its abstract point set. -/
theorem coherentExtension_preserves_triple
    (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (p q r : realizedPoint (graph P.triple) (localDiagram P))
    (h : realizedTriple (graph P.triple) (localDiagram P) p q r) :
    realizedTriple (graph P.triple) (localDiagram P)
      ((coherentExtension P U W hU hW f) p)
      ((coherentExtension P U W hU hW f) q)
      ((coherentExtension P U W hU hW f) r) := by
  let D := graph P.triple
  let L := localDiagram P
  let kU := domainPrefix P U hU
  let kW := domainPrefix P W hW
  let σ := OrderedCompletion.totalCompletion U W f
  let t := inputSymmetry P σ
  have h1 := realizedDeck_preserves_triple D L kU p q r h
  have h2 := relabelPointEquiv_preserves_triple D L t
    ((realizedDeck D L kU) p)
    ((realizedDeck D L kU) q)
    ((realizedDeck D L kU) r) h1
  have h3 := realizedDeck_preserves_triple D L kW
    ((relabelPointEquiv D L t) ((realizedDeck D L kU) p))
    ((relabelPointEquiv D L t) ((realizedDeck D L kU) q))
    ((relabelPointEquiv D L t) ((realizedDeck D L kU) r)) h2
  simpa only [coherentExtension, extensionMap, Equiv.trans_apply] using h3

end GluingEPPA.Steiner.InitialSites
