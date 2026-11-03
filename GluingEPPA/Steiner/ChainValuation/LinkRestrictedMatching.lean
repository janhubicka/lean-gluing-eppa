import GluingEPPA.Steiner.ChainValuation.ProjectorNaturality
import GluingEPPA.Steiner.ChainValuation.TwoGroupRestriction

/-!
# Restricted coset matching for the literal earlier-stage Link family

This instantiates the two-group matching at one actual chain attachment.
The required equality of subgroup pullbacks follows from the already
constructed smaller-stage links and the naturality of their projectors.
No embedding into the not-yet-constructed K_S is used.
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

/-- Intersecting M with the two adjacent block alphabets and pulling back
to their common alphabet gives the same earlier subgroup. -/
theorem mask_pullbacks_agree (M A B : Proper S) :
    (L (Step.meet S M A) A Finset.inter_subset_right).incl.range.comap
        (L (Step.meet S A B) A Finset.inter_subset_left).incl =
      (L (Step.meet S M B) B Finset.inter_subset_right).incl.range.comap
        (L (Step.meet S A B) B Finset.inter_subset_right).incl := by
  let I := Step.meet S A B
  let MA := Step.meet S M A
  let MB := Step.meet S M B
  have hleft := comap_range D S old L MA I A
    (show MA.val ⊆ A.val from Finset.inter_subset_right)
    (show I.val ⊆ A.val from Finset.inter_subset_left)
  have hright := comap_range D S old L MB I B
    (show MB.val ⊆ B.val from Finset.inter_subset_right)
    (show I.val ⊆ B.val from Finset.inter_subset_right)
  have hmask : Step.meet S MA I = Step.meet S MB I := by
    apply Subtype.ext
    ext e
    simp [Step.meet, MA, MB, I, Finset.mem_inter] <;> tauto
  change (L MA A Finset.inter_subset_right).incl.range.comap
      (L I A Finset.inter_subset_left).incl =
    (L MB B Finset.inter_subset_right).incl.range.comap
      (L I B Finset.inter_subset_right).incl
  calc
    _ = (L (Step.meet S MA I) I Finset.inter_subset_right).incl.range :=
      hleft
    _ = (L (Step.meet S MB I) I Finset.inter_subset_right).incl.range := by
      let F (n : Proper S) : Subgroup (old I).Carrier :=
        if h : n.val ⊆ I.val then (L n I h).incl.range else ⊥
      have hF := congrArg F hmask
      have hl : (Step.meet S MA I).val ⊆ I.val :=
        Finset.inter_subset_right
      have hr : (Step.meet S MB I).val ⊆ I.val :=
        Finset.inter_subset_right
      simpa only [F, dif_pos hl, dif_pos hr] using hF
    _ = _ := hright.symm

/-- The restricted component pieces across one actual chain attachment
form a partial matching, derived from the previous links. -/
def restrictedLinkMatching (M A B : Proper S) (h : (old A).Carrier) :
    ChainValuation.Matching
      (Sum (Set (old A).Carrier) (Set (old B).Carrier)) :=
  ChainValuation.twoGroupAttachmentMatching
    (L (Step.meet S A B) A Finset.inter_subset_left).incl
    (L (Step.meet S A B) B Finset.inter_subset_right).incl
    (L (Step.meet S M A) A Finset.inter_subset_right).incl.range
    (L (Step.meet S M B) B Finset.inter_subset_right).incl.range
    (mask_pullbacks_agree D S old L M A B) h

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
