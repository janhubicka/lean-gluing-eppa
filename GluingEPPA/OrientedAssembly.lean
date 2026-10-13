import GluingEPPA.OrientedCover

/-!
The unconditional EPPA theorem is reduced to constructing the distinguished
inverse-compatible permutation extensions.

This theorem is an actual finite relational EPPA witness for every *supplied*
PermutationDiagramData, with the enlarged oriented-edge Boolean cover.
No axiom asserts the existence of the permutation data.
-/
namespace GluingEPPA
universe u v w z
namespace PermutationDiagramData

variable {L : Nat → Type u} {A : Type v} {U : Type w} {I : Type z}
variable {S : RelStructure L A} (D : PermutationDiagramData S U I)

abbrev WitnessCarrier : Type _ := (D.orientedGraph.cover D.system).Realization

def witness : RelStructure L D.WitnessCarrier :=
  (D.orientedGraph.cover D.system).quotientStructure S

/-- The root copy is an induced embedding in the explicitly indexed witness. -/
noncomputable def inclusion [Fintype U] [Fintype I] : Embedding S D.witness := by
  classical
  exact D.rootEmbedding

/-- All chosen partial automorphisms have simultaneous extensions on one witness. -/
theorem all_extensions [Fintype U] [Fintype I] :
    ∀ i : I, ∃ φ : D.WitnessCarrier ≃ D.WitnessCarrier,
      (∀ {n : Nat} (r : L n) (q : Fin n → D.WitnessCarrier),
        D.witness.rel r (fun j => φ (q j)) ↔ D.witness.rel r q) ∧
      (∀ x y : A, D.transport i x y →
        φ (D.inclusion.toFun x) = D.inclusion.toFun y) := by
  classical
  intro i
  refine ⟨(D.liftedSymmetry i).quotientEquiv, ?_, ?_⟩
  · intro n r q
    exact (D.liftedSymmetry i).rel_iff S r q
  · intro x y h
    exact D.extends_transport i h

/-- A finite induced relational witness with extension of every indexed map.
This is conditional only on the explicit finite permutation data D. -/
theorem finite_eppa_for_data [Fintype A] [Fintype U] [Fintype I] :
    Finite D.WitnessCarrier ∧
    (∃ ι : Embedding S D.witness,
      ∀ i : I, ∃ φ : D.WitnessCarrier ≃ D.WitnessCarrier,
        (∀ {n : Nat} (r : L n) (q : Fin n → D.WitnessCarrier),
          D.witness.rel r (fun j => φ (q j)) ↔ D.witness.rel r q) ∧
        (∀ x y : A, D.transport i x y → φ (ι.toFun x) = ι.toFun y)) := by
  classical
  refine ⟨D.finite_witness, D.inclusion, ?_⟩
  exact D.all_extensions

end PermutationDiagramData
end GluingEPPA
