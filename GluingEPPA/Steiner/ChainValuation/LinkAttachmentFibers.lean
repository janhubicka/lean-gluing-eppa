import GluingEPPA.Steiner.ChainValuation.AttachmentFibers
import GluingEPPA.Steiner.ChainValuation.LinkRestrictedMatching

/-!
# Whole attachment fibres for the actual earlier-stage links

At a chain attachment between the older K_A and K_B blocks, every smaller-mask
coset meets their common subgroup along precisely one coset of the triple mask
K_(M∩A∩B). This is a statement about *all points* on the attachment and does
not rely on a common ambient large group.
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

/-- Pointwise correspondence of restricted cosets through the common
attaching group. This is stronger than merely saying that two pieces meet. -/
theorem restrictedLink_fibre_mem_iff
    (M A B : Proper S)
    (h : (old A).Carrier)
    (k z : (old (Step.meet S A B)).Carrier) :
    h * (L (Step.meet S A B) A Finset.inter_subset_left).incl z ∈
        ChainValuation.leftCoset
          (L (Step.meet S M A) A Finset.inter_subset_right).incl.range
          (h * (L (Step.meet S A B) A Finset.inter_subset_left).incl k) ↔
    (L (Step.meet S A B) B Finset.inter_subset_right).incl z ∈
        ChainValuation.leftCoset
          (L (Step.meet S M B) B Finset.inter_subset_right).incl.range
          ((L (Step.meet S A B) B Finset.inter_subset_right).incl k) := by
  exact ChainValuation.two_group_attachment_mem_iff
    (L (Step.meet S A B) A Finset.inter_subset_left).incl
    (L (Step.meet S A B) B Finset.inter_subset_right).incl
    (L (Step.meet S M A) A Finset.inter_subset_right).incl.range
    (L (Step.meet S M B) B Finset.inter_subset_right).incl.range
    (mask_pullbacks_agree D S old L M A B) h k z

/-- The entire old-side attaching intersection is one translated coset of
the restricted common group. -/
theorem restrictedLink_fibre_inter
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (Step.meet S A B)).Carrier) :
    ChainValuation.leftCoset
        (L (Step.meet S M A) A Finset.inter_subset_right).incl.range
        (h * (L (Step.meet S A B) A Finset.inter_subset_left).incl k)
      ∩ ChainValuation.leftCoset
        (L (Step.meet S A B) A Finset.inter_subset_left).incl.range h =
      {x : (old A).Carrier |
        ∃ z : (old (Step.meet S A B)).Carrier,
          z ∈ ChainValuation.leftCoset
            (((L (Step.meet S M A) A Finset.inter_subset_right).incl.range).comap
              (L (Step.meet S A B) A Finset.inter_subset_left).incl) k ∧
          x = h * (L (Step.meet S A B) A Finset.inter_subset_left).incl z} := by
  exact ChainValuation.attachment_intersection_exact
    (L (Step.meet S A B) A Finset.inter_subset_left).incl
    (L (Step.meet S M A) A Finset.inter_subset_right).incl.range h k

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
