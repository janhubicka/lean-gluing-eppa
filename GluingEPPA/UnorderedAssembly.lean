import GluingEPPA.UnorderedCover

/-!
The finite EPPA witness assembled with Sofia's *literal* unordered edge set.
Every base edge carries a single Boolean coordinate.
-/
namespace GluingEPPA
universe u v w z
namespace PermutationDiagramData
variable {L : Nat → Type u} {A : Type v} {U : Type w} {I : Type z}
variable {S : RelStructure L A} (D : PermutationDiagramData S U I)
variable [DecidableEq D.unorderedEdges]

abbrev UnorderedWitnessCarrier : Type _ := (D.unorderedGraph.cover D.system).Realization

noncomputable def unorderedWitness : RelStructure L D.UnorderedWitnessCarrier :=
  (D.unorderedGraph.cover D.system).quotientStructure S

noncomputable def unorderedInclusion [Fintype U] [Fintype I] :
    Embedding S D.unorderedWitness :=
  D.unorderedEmbedding

theorem unordered_all_extensions [Fintype U] [Fintype I] :
    ∀ i : I, ∃ φ : D.UnorderedWitnessCarrier ≃ D.UnorderedWitnessCarrier,
      (∀ {n : Nat} (r : L n) (q : Fin n → D.UnorderedWitnessCarrier),
        D.unorderedWitness.rel r (fun j => φ (q j)) ↔
          D.unorderedWitness.rel r q) ∧
      (∀ x y : A, D.transport i x y →
        φ (D.unorderedInclusion.toFun x) = D.unorderedInclusion.toFun y) := by
  intro i
  refine ⟨(D.unorderedLiftedSymmetry i).quotientEquiv, ?_, ?_⟩
  · intro n r q
    exact (D.unorderedLiftedSymmetry i).rel_iff S r q
  · intro x y h
    exact D.unordered_extends_transport i h

/-- The exact undirected-edge EPPA conclusion, conditional only on explicit
finite permutation data, with no relational realization supplied. -/
theorem finite_eppa_for_data_unordered [Fintype A] [Fintype U] [Fintype I] :
    Finite D.UnorderedWitnessCarrier ∧
    (∃ ι : Embedding S D.unorderedWitness,
      ∀ i : I, ∃ φ : D.UnorderedWitnessCarrier ≃ D.UnorderedWitnessCarrier,
        (∀ {n : Nat} (r : L n) (q : Fin n → D.UnorderedWitnessCarrier),
          D.unorderedWitness.rel r (fun j => φ (q j)) ↔
            D.unorderedWitness.rel r q) ∧
        (∀ x y : A, D.transport i x y →
          φ (ι.toFun x) = ι.toFun y)) := by
  refine ⟨D.finite_unordered_witness, D.unorderedInclusion, ?_⟩
  exact D.unordered_all_extensions

end PermutationDiagramData
end GluingEPPA
