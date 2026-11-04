import GluingEPPA.Steiner.ChainValuation.MatchedLinkCosetRestriction
import GluingEPPA.Steiner.ChainValuation.ChainState

/-!
# Actual restricted Link cosets are closed under genuine M-edges

The matched restriction from the preceding module selects the literal
left cosets of K_(M∩A) and K_(M∩B) in the adjacent earlier groups.

The subgroup of each earlier group contains all its genuine generators
whose colours belong to M. Consequently an M-edge starting in either
selected coset stays in that coset. This discharges, on *actual*
Link Cayley blocks, the local edge-closure premise needed to show
M-saturation of a restricted exact pushout.

This is one boundary, not the normalized full-chain theorem.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u}

/-- A left coset of a subgroup containing all permitted named
generators is closed under every genuine edge of those colours.
The argument works for noncommutative groups. -/
theorem GroupBlock.leftCoset_closed_under_mask
    (B : GroupBlock.{u,v} E)
    (M : Finset E) (P : Subgroup B.Carrier)
    (hgen : ∀ letter, letter ∈ M →
      letter ∈ B.active → B.edge letter ∈ P)
    (base : B.Carrier)
    (letter : E) (he : letter ∈ M)
    (x y : B.Carrier)
    (hxy : (B.matching letter).Rel x y)
    (hx : x ∈ leftCoset P base) :
    y ∈ leftCoset P base := by
  obtain ⟨ha, hval⟩ := hxy
  change base⁻¹ * y ∈ P
  rw [hval]
  rw [← mul_assoc]
  exact P.mul_mem hx (hgen letter he ha)

end GluingEPPA.Steiner.ChainValuation

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

/-- The actual inclusion K_(M∩A) → K_A contains each named
generator from M∩A, without any ambient K_S. -/
theorem restrictedLink_generator_mem
    (M A : Proper S) (letter : E)
    (heM : letter ∈ M.val) (heA : letter ∈ A.val) :
    (block S old A).edge letter ∈
      (L (Step.meet S M A) A Finset.inter_subset_right).incl.range := by
  let T := Step.meet S M A
  have heT : letter ∈ T.val :=
    Finset.mem_inter.mpr ⟨heM, heA⟩
  exact ⟨(old T).edge letter,
    (L T A Finset.inter_subset_right).incl_edge letter heT⟩

/-- Both actual restricted coset pieces of a Link attachment are
individually closed under all their genuine M-labelled edges. -/
theorem matchedLinkCoset_edges_closed
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier) :
    (∀ letter ∈ M.val,
      ∀ x y : (old A).Carrier,
        ((block S old A).matching letter).Rel x y →
        x ∈ (matchedLinkCosetRestriction D S old L M A B h k).left →
        y ∈ (matchedLinkCosetRestriction D S old L M A B h k).left) ∧
    (∀ letter ∈ M.val,
      ∀ x y : (old B).Carrier,
        ((block S old B).matching letter).Rel x y →
        x ∈ (matchedLinkCosetRestriction D S old L M A B h k).right →
        y ∈ (matchedLinkCosetRestriction D S old L M A B h k).right) := by
  constructor
  · intro letter he x y hxy hx
    exact GroupBlock.leftCoset_closed_under_mask
      (block S old A) M.val
      (L (Step.meet S M A) A Finset.inter_subset_right).incl.range
      (fun e hm ha =>
        restrictedLink_generator_mem D S old L M A e hm ha)
      (h * left D S old L A B k) letter he x y hxy hx
  · intro letter he x y hxy hx
    exact GroupBlock.leftCoset_closed_under_mask
      (block S old B) M.val
      (L (Step.meet S M B) B Finset.inter_subset_right).incl.range
      (fun e hm hb =>
        restrictedLink_generator_mem D S old L M B e hm hb)
      (right D S old L A B k) letter he x y hxy hx

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
