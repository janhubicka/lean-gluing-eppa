import GluingEPPA.Steiner.ChainValuation.RestrictedPushoutExact
import GluingEPPA.Steiner.ChainValuation.LinkAttachmentFibers
import GluingEPPA.Steiner.ChainValuation.GroupAttachment
import GluingEPPA.Steiner.ChainValuation.LinkChain

/-!
# Matched restrictions for the literal earlier-stage Link cosets

Fix two earlier Cayley blocks K_A and K_B of a separated chain and an
actual attachment parameter k in their common group K_(A∩B).
The restricted M-components passing through that parameter are
left cosets of the literal earlier subgroups K_(M∩A) and K_(M∩B).

The already-checked Link fibre theorem says their entire attaching
preimages agree. Consequently these two genuine cosets form a
MatchedRestriction, and the exact restricted-pushout theorem applies
without any additional compatibility hypothesis.

This is a *one-attachment* normalization fact; constructing the
selected interval of cosets in an arbitrary chain remains open.
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

/-- The actual two adjacent restricted Cayley cosets meeting at
the prescribed earlier-stage Link attaching parameter k.
Agreement of their entire attaching fibres is proved, not assumed. -/
noncomputable def matchedLinkCosetRestriction
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier) :
    MatchedRestriction
      (attachLeft h (left D S old L A B))
      (right D S old L A B) where
  left :=
    leftCoset
      (L (Step.meet S M A) A Finset.inter_subset_right).incl.range
      (h * left D S old L A B k)
  right :=
    leftCoset
      (L (Step.meet S M B) B Finset.inter_subset_right).incl.range
      (right D S old L A B k)
  agree := by
    intro z
    exact restrictedLink_fibre_mem_iff D S old L M A B h k z

/-- The selected attachment parameters form one exact coset of the
pullback of the old restricted subgroup, centred at k.
In particular, this is a *whole* interface, not a chosen point. -/
theorem matchedLinkCoset_interface_iff
    (M A B : Proper S) (h : (old A).Carrier)
    (k z : (old (common S A B)).Carrier) :
    attachLeft h (left D S old L A B) z ∈
      (matchedLinkCosetRestriction D S old L M A B h k).left ↔
    z ∈ leftCoset
      ((L (Step.meet S M A) A Finset.inter_subset_right).incl.range.comap
        (left D S old L A B)) k := by
  change
    (h * left D S old L A B k)⁻¹ *
      (h * left D S old L A B z) ∈
        (L (Step.meet S M A) A Finset.inter_subset_right).incl.range ↔
      k⁻¹ * z ∈
        (L (Step.meet S M A) A Finset.inter_subset_right).incl.range.comap
          (left D S old L A B)
  have heq :
      (h * left D S old L A B k)⁻¹ *
        (h * left D S old L A B z) =
      left D S old L A B (k⁻¹ * z) := by
    simp only [map_mul, map_inv]
    group
  rw [heq]
  rfl

/-- Exact smaller pushout for the *literal* matched M-cosets.
The target is their entire union inside the true group attachment,
not an arbitrary surjective cover or a hypothetical ambient K_S. -/
noncomputable def matchedLinkCoset_equivCovered
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier) :
    let R := matchedLinkCosetRestriction D S old L M A B h k
    let i := left D S old L A B
    let j := right D S old L A B
    R.Space
      (attachLeft_injective h i (left_injective D S old L A B))
      (right_injective D S old L A B) ≃
    {q :
      SetPushout (attachLeft h i) j
        (attachLeft_injective h i (left_injective D S old L A B))
        (right_injective D S old L A B) //
      q ∈ R.Covered
        (attachLeft_injective h i (left_injective D S old L A B))
        (right_injective D S old L A B)} :=
  (matchedLinkCosetRestriction D S old L M A B h k).equivCovered
    (attachLeft_injective h (left D S old L A B)
      (left_injective D S old L A B))
    (right_injective D S old L A B)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
