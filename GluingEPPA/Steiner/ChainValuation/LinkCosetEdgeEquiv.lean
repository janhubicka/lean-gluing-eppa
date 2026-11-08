import GluingEPPA.Steiner.ChainValuation.LinkCayleyMask

/-!
# Genuine letter-edge reflection by the normalized earlier Cayley chart

The chain-restriction normal form uses translated left cosets of the
actual included group K_(M∩A) inside each earlier block K_A.
The map x ↦ g·incl(x) reflects as well as preserves every genuine
edge of a letter in M. This is the precise local edge statement
needed before transporting completed fixed-point involutions.
No commutativity or normality of the subgroup is assumed.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- Left translation of the literal earlier Link inclusion reflects
every genuine M-coloured right Cayley edge, including the case where
a letter belongs to M but not to the block alphabet A. -/
theorem restrictedBlock_translation_edge_iff
    (M A : Proper S) (g : (old A).Carrier)
    (e : E) (heM : e ∈ M.val)
    (x y : (old (Step.meet S M A)).Carrier) :
    ((block S old (Step.meet S M A)).matching e).Rel x y ↔
    ((block S old A).matching e).Rel
      (g * (L (Step.meet S M A) A Finset.inter_subset_right).incl x)
      (g * (L (Step.meet S M A) A Finset.inter_subset_right).incl y) := by
  let T : Proper S := Step.meet S M A
  let i : (old T).Carrier →* (old A).Carrier :=
    (L T A Finset.inter_subset_right).incl
  have hi : Function.Injective i :=
    Link.injective D (old T) (old A)
      Finset.inter_subset_right (L T A Finset.inter_subset_right)
  change
    (e ∈ T.val ∧ y = x * (old T).edge e) ↔
      (e ∈ A.val ∧ g * i y = (g * i x) * (old A).edge e)
  constructor
  · rintro ⟨heT, hy⟩
    have heA : e ∈ A.val := (Finset.mem_inter.mp heT).2
    refine ⟨heA, ?_⟩
    calc
      g * i y = g * i (x * (old T).edge e) := by rw [hy]
      _ = (g * i x) * i ((old T).edge e) := by simp [map_mul, mul_assoc]
      _ = (g * i x) * (old A).edge e := by
        rw [(L T A Finset.inter_subset_right).incl_edge e heT]
  · rintro ⟨heA, hy⟩
    have heT : e ∈ T.val := Finset.mem_inter.mpr ⟨heM, heA⟩
    refine ⟨heT, ?_⟩
    apply hi
    apply mul_left_cancel (a := g)
    calc
      g * i y = (g * i x) * (old A).edge e := hy
      _ = (g * i x) * i ((old T).edge e) := by
        rw [(L T A Finset.inter_subset_right).incl_edge e heT]
      _ = g * i (x * (old T).edge e) := by simp [map_mul, mul_assoc]

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
