import GluingEPPA.RelPartialAut
import GluingEPPA.OrientedAssembly

/-!
Unconditional EPPA for any finite relational structure: every partial
automorphism is a label; the finite family of their transport relations
is extended coherently and padded, then the oriented Boolean cover
provides one finite induced witness and all extending automorphisms.

The witness uses an oriented-edge Boolean cover, an intentionally larger
equivalent-existence construction than Sofia's undirected-edge cover.
-/
namespace GluingEPPA
universe u v

/-- No assumption about an EPPA witness or coherent total extensions:
all data are constructed from the finite input relational structure. -/
theorem finite_relational_eppa
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
  letI : DecidableEq ((U ≃ U) × I) := Classical.decEq _
  let D : PermutationDiagramData S U I := F.baseFamily.paddedData
  obtain ⟨hfinite, ⟨ι, hext⟩⟩ := D.finite_eppa_for_data
  refine ⟨D.WitnessCarrier, D.witness, ι, hfinite, ?_⟩
  intro f
  obtain ⟨φ, hrel, hmap⟩ := hext f
  refine ⟨φ, hrel, ?_⟩
  intro x y h
  exact hmap x y h

end GluingEPPA
