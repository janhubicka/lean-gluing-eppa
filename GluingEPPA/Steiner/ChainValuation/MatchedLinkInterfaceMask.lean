import GluingEPPA.Steiner.ChainValuation.MatchedLinkCosetSaturation
import GluingEPPA.Steiner.ChainValuation.ProjectorNaturality

/-!
# The actual restricted interface is the earlier triple-mask subgroup

At the boundary K_A -- K_(A∩B) -- K_B, let I=A∩B.
A restriction to M selects cosets of the earlier groups K_(M∩A)
and K_(M∩B). The entire selected attaching fibre in K_I is a
coset of the literal image of K_(M∩I).

This follows from the previously checked projector-naturality
comap theorem and the ordinary intersection identities for
finite masks. It makes the *whole* smaller-chain interface
explicit, rather than simply assuming it is isomorphic to one.
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

/-- Pulling the restriction subgroup K_(M∩A) back to the
actual common attaching group K_(A∩B) gives precisely the
included subgroup K_(M∩A∩B), with no outside generators. -/
theorem matchedLinkCoset_interface_subgroup
    (M A B : Proper S) :
    (L (Step.meet S M A) A Finset.inter_subset_right).incl.range.comap
        (left D S old L A B) =
      (L (Step.meet S M (common S A B)) (common S A B)
        Finset.inter_subset_right).incl.range := by
  let I : Proper S := common S A B
  let MA : Proper S := Step.meet S M A
  have hcomap :=
    comap_range D S old L MA I A
      Finset.inter_subset_right Finset.inter_subset_left
  have hindex : Step.meet S MA I = Step.meet S M I := by
    apply Subtype.ext
    ext e
    simp [Step.meet, MA, I, common, Finset.mem_inter] <;> tauto
  change
    (L MA A Finset.inter_subset_right).incl.range.comap
        (L I A Finset.inter_subset_left).incl =
      (L (Step.meet S M I) I Finset.inter_subset_right).incl.range
  calc
    _ =
      (L (Step.meet S MA I) I Finset.inter_subset_right).incl.range :=
        hcomap
    _ =
      (L (Step.meet S M I) I Finset.inter_subset_right).incl.range := by
        let F (n : Proper S) : Subgroup (old I).Carrier :=
          if h : n.val ⊆ I.val then (L n I h).incl.range else ⊥
        have hF := congrArg F hindex
        have hl : (Step.meet S MA I).val ⊆ I.val :=
          Finset.inter_subset_right
        have hr : (Step.meet S M I).val ⊆ I.val :=
          Finset.inter_subset_right
        simpa only [F, dif_pos hl, dif_pos hr] using hF

/-- Every attaching point in the matched component pieces is
indexed by exactly one coset of the genuine earlier group
K_(M∩A∩B) in the common attaching group K_(A∩B). -/
theorem matchedLinkCoset_interface_exact_iff
    (M A B : Proper S) (h : (old A).Carrier)
    (k z : (old (common S A B)).Carrier) :
    attachLeft h (left D S old L A B) z ∈
        (matchedLinkCosetRestriction D S old L M A B h k).left ↔
      z ∈ leftCoset
        (L (Step.meet S M (common S A B)) (common S A B)
          Finset.inter_subset_right).incl.range k := by
  rw [matchedLinkCoset_interface_iff D S old L M A B h k z,
    matchedLinkCoset_interface_subgroup D S old L M A B]

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
