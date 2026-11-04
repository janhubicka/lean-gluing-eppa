import GluingEPPA.Steiner.ChainValuation.MatchedLinkCosetSaturation
import GluingEPPA.Steiner.ChainValuation.LinkProjectors

/-!
# The genuine restricted attachment interface is the triple-mask group

The exact smaller pushout of two matched M-coset pieces is attached
along one coset of the pullback subgroup in K_(A∩B). The earlier Link
projector identity identifies that subgroup with the image of the
*actual* already constructed group K_(M∩A∩B).

This proves the interface used by the normalized smaller-mask chain
is not an arbitrary subgroup or an invented quotient. All groups are
earlier stages; there is no assumed ambient K_S.

The full multi-block normalization remains a separate obligation.
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

/-- Pulling K_(M∩A) back to the attachment K_(A∩B)
gives precisely the embedded K_(M∩A∩B), in its actual earlier
stage, without any full K_S. -/
theorem restrictedLink_common_comap_eq
    (M A B : Proper S) :
    (L (Step.meet S M A) A Finset.inter_subset_right).incl.range.comap
      (left D S old L A B) =
    (L (Step.meet S M (common S A B)) (common S A B)
      Finset.inter_subset_right).incl.range := by
  let I := common S A B
  let MA := Step.meet S M A
  have hsource := comap_range D S old L MA I A
    (show MA.val ⊆ A.val from Finset.inter_subset_right)
    (show I.val ⊆ A.val from Finset.inter_subset_left)
  have hmask : Step.meet S MA I = Step.meet S M I := by
    apply Subtype.ext
    ext e
    simp [Step.meet, MA, I, common, Finset.mem_inter] <;> tauto
  change (L MA A Finset.inter_subset_right).incl.range.comap
      (L I A Finset.inter_subset_left).incl =
    (L (Step.meet S M I) I Finset.inter_subset_right).incl.range
  calc
    _ = (L (Step.meet S MA I) I Finset.inter_subset_right).incl.range :=
      hsource
    _ = (L (Step.meet S M I) I Finset.inter_subset_right).incl.range := by
      let F (n : Proper S) : Subgroup (old I).Carrier :=
        if h : n.val ⊆ I.val then (L n I h).incl.range else ⊥
      have hF := congrArg F hmask
      have hl : (Step.meet S MA I).val ⊆ I.val :=
        Finset.inter_subset_right
      have hr : (Step.meet S M I).val ⊆ I.val :=
        Finset.inter_subset_right
      simpa only [F, dif_pos hl, dif_pos hr] using hF

/-- The *entire* interface of the two matched actual M-coset
pieces is exactly a left coset of the embedded
K_(M∩A∩B) inside K_(A∩B), centred at the attachment k. -/
theorem matchedLinkCoset_triple_interface_iff
    (M A B : Proper S) (h : (old A).Carrier)
    (k z : (old (common S A B)).Carrier) :
    attachLeft h (left D S old L A B) z ∈
        (matchedLinkCosetRestriction D S old L M A B h k).left ↔
      z ∈ leftCoset
        (L (Step.meet S M (common S A B)) (common S A B)
          Finset.inter_subset_right).incl.range k := by
  rw [matchedLinkCoset_interface_iff D S old L M A B h k z]
  rw [restrictedLink_common_comap_eq D S old L M A B]

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
