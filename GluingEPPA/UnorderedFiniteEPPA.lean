import GluingEPPA.UnorderedAssembly
import GluingEPPA.RelPartialAut

/-!
Unconditional finite relational EPPA using precisely the undirected-edge
Boolean coordinates of the written gluing construction, rather than the
larger oriented occurrence indexing.

The only remaining discrepancy from Sofia's manuscript is the separate
private-cycle marker bound: the chosen distinguished permutations here
are constructed using the already checked ZMod4 marker method.
-/
namespace GluingEPPA
universe u v

theorem finite_relational_eppa_unordered
    {L : Nat → Type u} {A : Type v} [Finite A] (S : RelStructure L A) :
    ∃ (B : Type v) (T : RelStructure L B) (ι : Embedding S T),
      Finite B ∧
      ∀ f : RelPartialAut S,
        ∃ φ : B ≃ B,
          (∀ {n : Nat} (r : L n) (q : Fin n → B),
            T.rel r (fun j => φ (q j)) ↔ T.rel r q) ∧
          (∀ x y : A, f.val x = some y →
            φ (ι.toFun x) = ι.toFun y) := by
  classical
  let I := RelPartialAut S
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype I := Fintype.ofFinite I
  letI : LinearOrder I := RelPartialAut.chosenOrder S
  let F : PartialFamily S I := RelPartialAut.family S
  let U := BaseFamily.PaddedCarrier A I
  letI : Fintype U := Fintype.ofFinite U
  let D : PermutationDiagramData S U I := F.baseFamily.paddedData
  letI : DecidableEq D.unorderedEdges := Classical.decEq _
  obtain ⟨hfinite, ⟨ι, hext⟩⟩ := D.finite_eppa_for_data_unordered
  refine ⟨D.UnorderedWitnessCarrier, D.unorderedWitness, ι, hfinite, ?_⟩
  intro f
  obtain ⟨φ, hrel, hmap⟩ := hext f
  refine ⟨φ, hrel, ?_⟩
  intro x y h
  exact hmap x y h

end GluingEPPA
