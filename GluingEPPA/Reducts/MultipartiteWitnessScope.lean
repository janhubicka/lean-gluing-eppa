import GluingEPPA.Reducts.MultipartiteLocalWitness

/-! Semantic correspondence and the actual (larger) finite witness size.
The partition is recovered from the digraph: it is not a hidden named sort.
-/
namespace GluingEPPA.Reducts.MultipartiteWitnessScope
open GluingEPPA.Reducts.PairValuationConjugation
open GluingEPPA.Reducts.MultipartiteConcreteCarrier
open GluingEPPA.Reducts.MultipartiteActualLocalActions
open GluingEPPA.Reducts.MultipartiteLocalWitness

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {A I : Type u} [Fintype A] [Fintype I]

theorem same_part_iff (S : Input A I) (x y : A) :
    S.owner x = S.owner y ↔ S.color x y = false ∧ S.color y x = false := by
  constructor
  · intro h
    exact ⟨S.within x y h, S.within y x h.symm⟩
  · intro h
    by_contra hne
    have hr := S.reverse x y hne
    rw [h.1, h.2] at hr
    cases hr

/-- No extra part-preservation condition is imposed on digraph automorphisms. -/
def localAutOfColor (S : Input A I) (D : Set A) (p : BasePerm D)
    (hc : ∀ x y, S.color (p.forward x).val (p.forward y).val = S.color x.val y.val) :
    LocalAut S D where
  perm := p
  part_iff := by
    intro x y
    rw [same_part_iff, same_part_iff, hc, hc]
  color_eq := hc

theorem witness_owner_surjective :
    Function.Surjective (witness (A := A) (I := I)).owner := by
  intro i
  exact ⟨((i, ⟨0, Nat.factorial_pos _⟩), fun _ => false), rfl⟩

/-- This is the actual full-row factorial witness, not the sharper paper bound. -/
theorem witness_card :
    Fintype.card (Carrier A I) =
      (Fintype.card I * padding A) * 2 ^ (Fintype.card I * padding A) := by
  simp [Carrier, Vertex, Base]

end
end GluingEPPA.Reducts.MultipartiteWitnessScope
