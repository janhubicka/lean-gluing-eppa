import GluingEPPA.Sparsening.AtlasIrreducible

/-!
# Faithfulness and the projection for the canonical orbit atlas

The previous generic lemma is instantiated on the concrete, automorphism-
invariant family of closed subcharts. This is the exact bridge from the
survey's definition of irreducibility to automorphic faithfulness.

The whole bounded-tree sparsening theorem still needs a separate induction.
-/
namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v w
variable {L : Nat → Type u} {A : Type v} {F : Type w}
variable (R : RelStructure L A) (out : F → A → Set A) (root : Set A)
variable [Finite A]
open scoped Classical
noncomputable section
attribute [local instance] chartsFintype edgesFintype

/-- On each nonempty irreducible closed substructure of the canonical orbit
refinement the projection is a genuine homomorphism-embedding, with exact
whole unary fibres, not merely a weak relational homomorphism. -/
theorem projection_on_irreducible (X : Set (Vertex R out root)) [Nonempty X]
    (hclosed : UnaryClosed (outputs R out root) (fun q => q ∈ X))
    (hirr : IsIrreducible
      (ChartAtlas.inducedAtlas (graph R out root) (support R out root) R X)
      (ChartAtlas.inducedOutput (graph R out root) (support R out root)
        out (closed R out root) X)) :
    ChartAtlas.ProjectionIsEmbeddingOn (graph R out root) (support R out root)
      R out (closed R out root) X :=
  ChartAtlas.project_embeds_irreducible
    (graph R out root) (support R out root)
    R out (closed R out root) CompleteChartGraph.complete X hclosed hirr

/-- Actual automorphic faithfulness: every nonempty irreducible closed test
is moved INTO the distinguished root copy. No chart transitivity or upstairs
automorphism has been supplied as a hypothesis. -/
theorem irreducible_move_into_root
    (hr : UnaryClosed out (fun x => x ∈ root))
    (X : Set (Vertex R out root)) [Nonempty X]
    (hclosed : UnaryClosed (outputs R out root) (fun q => q ∈ X))
    (hirr : IsIrreducible
      (ChartAtlas.inducedAtlas (graph R out root) (support R out root) R X)
      (ChartAtlas.inducedOutput (graph R out root) (support R out root)
        out (closed R out root) X)) :
    ∃ a : Aut (relations R out root) (outputs R out root),
      ∀ q : Vertex R out root, q ∈ X →
        a.perm q ∈ liftedChart R out root (rootChart R out root hr) 0 := by
  obtain ⟨s, chi, hchart⟩ :=
    ChartAtlas.irreducible_lies_in_chart
      (graph R out root) (support R out root) R out
      (closed R out root) CompleteChartGraph.complete X hclosed hirr
  obtain ⟨a, ha⟩ := chart_to_root R out root hr s chi
  refine ⟨a, ?_⟩
  intro q hq
  obtain ⟨hs, heq⟩ := hchart ⟨q, hq⟩
  have hm : q ∈ liftedChart R out root s chi :=
    ⟨ChartAtlas.project (graph R out root) (support R out root) q, hs, heq⟩
  exact ha ⟨q, hm, rfl⟩

end
end GluingEPPA.Sparsening.OrbitAtlas
