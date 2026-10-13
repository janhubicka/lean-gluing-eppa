import GluingEPPA.PaddedPrivateFamily
import GluingEPPA.UnorderedAssembly
import GluingEPPA.RelPartialAut

/-!
The exact unordered-edge Boolean gluing proof with the private two- and
three-cycle padding. Unlike finite_relational_eppa_unordered, this has only
two private slots per inverse-indexed partial automorphism. The additive
bound for the padded base permutation set is privateCarrier_card.
-/
namespace GluingEPPA
universe u v

/-- Unconditional finite relational EPPA, using the manuscript's unordered
Boolean edge set AND the private linear-size marker padding. -/
theorem finite_relational_eppa_private
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
  let U := BaseFamily.PrivatePaddedCarrier A I
  letI : Fintype U := Fintype.ofFinite U
  let D : PermutationDiagramData S U I := F.baseFamily.privateData
  letI : DecidableEq D.unorderedEdges := Classical.decEq _
  obtain ⟨hfinite, ⟨ι, hext⟩⟩ := D.finite_eppa_for_data_unordered
  refine ⟨D.UnorderedWitnessCarrier, D.unorderedWitness, ι, hfinite, ?_⟩
  intro f
  obtain ⟨φ, hrel, hmap⟩ := hext f
  refine ⟨φ, hrel, ?_⟩
  intro x y h
  exact hmap x y h

end GluingEPPA
