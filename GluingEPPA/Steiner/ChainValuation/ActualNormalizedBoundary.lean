import GluingEPPA.Steiner.ChainValuation.NormalizedBoundarySquare
import GluingEPPA.Steiner.ChainValuation.LinkProjectors
import GluingEPPA.Steiner.ChainValuation.LinkChain

/-!
# Normalized boundary squares in the actual earlier Link family

The generic noncommutative boundary formula is now specialized to the
literal earlier-stage groups K_A, K_B, K_(A∩B), K_(M∩A), K_(M∩B)
and K_(M∩A∩B). All commuting squares follow directly from the
existing Link generator identities, not additional hypotheses.

This identifies the precise normalized glueing equation at each
actual chain boundary. Building the complete restricted component
chain and proving its global quotient equivalence remain pending.
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

private theorem commonMask_left_subset (M A B : Proper S) :
    (Step.meet S M (common S A B)).val ⊆
      (Step.meet S M A).val := by
  intro e he
  have hm : e ∈ M.val := (Finset.mem_inter.mp he).1
  have hI : e ∈ (common S A B).val := (Finset.mem_inter.mp he).2
  exact Finset.mem_inter.mpr ⟨hm, (Finset.mem_inter.mp hI).1⟩

private theorem commonMask_right_subset (M A B : Proper S) :
    (Step.meet S M (common S A B)).val ⊆
      (Step.meet S M B).val := by
  intro e he
  have hm : e ∈ M.val := (Finset.mem_inter.mp he).1
  have hI : e ∈ (common S A B).val := (Finset.mem_inter.mp he).2
  exact Finset.mem_inter.mpr ⟨hm, (Finset.mem_inter.mp hI).2⟩

/-- The full common triple-mask group maps into the M-restricted
old block using only already constructed Link inclusions. -/
noncomputable def normalizedCommonLeft (M A B : Proper S) :
    (old (Step.meet S M (common S A B))).Carrier →*
    (old (Step.meet S M A)).Carrier :=
  (L (Step.meet S M (common S A B)) (Step.meet S M A)
    (commonMask_left_subset S M A B)).incl

noncomputable def normalizedCommonRight (M A B : Proper S) :
    (old (Step.meet S M (common S A B))).Carrier →*
    (old (Step.meet S M B)).Carrier :=
  (L (Step.meet S M (common S A B)) (Step.meet S M B)
    (commonMask_right_subset S M A B)).incl

noncomputable def normalizedCommonInterface (M A B : Proper S) :
    (old (Step.meet S M (common S A B))).Carrier →*
    (old (common S A B)).Carrier :=
  (L (Step.meet S M (common S A B)) (common S A B)
    Finset.inter_subset_right).incl

/-- In the actual earlier Link groups, both ways of including
the triple-mask group into K_A are identical. -/
theorem normalizedCommon_left_square (M A B : Proper S) :
    (L (Step.meet S M A) A Finset.inter_subset_right).incl.comp
      (normalizedCommonLeft D S old L M A B) =
    (left D S old L A B).comp
      (normalizedCommonInterface D S old L M A B) := by
  let J : Proper S := Step.meet S M (common S A B)
  let TA : Proper S := Step.meet S M A
  let I : Proper S := common S A B
  apply (old J).hom_ext
  intro e he
  have heTA : e ∈ TA.val := commonMask_left_subset S M A B he
  have heI : e ∈ I.val := Finset.inter_subset_right he
  change
    (L TA A Finset.inter_subset_right).incl
      ((L J TA (commonMask_left_subset S M A B)).incl ((old J).edge e)) =
    (L I A Finset.inter_subset_left).incl
      ((L J I Finset.inter_subset_right).incl ((old J).edge e))
  rw [(L J TA (commonMask_left_subset S M A B)).incl_edge e he,
    (L TA A Finset.inter_subset_right).incl_edge e heTA,
    (L J I Finset.inter_subset_right).incl_edge e he,
    (L I A Finset.inter_subset_left).incl_edge e heI]

/-- The same commuting Link square on the new side K_B. -/
theorem normalizedCommon_right_square (M A B : Proper S) :
    (L (Step.meet S M B) B Finset.inter_subset_right).incl.comp
      (normalizedCommonRight D S old L M A B) =
    (right D S old L A B).comp
      (normalizedCommonInterface D S old L M A B) := by
  let J : Proper S := Step.meet S M (common S A B)
  let TB : Proper S := Step.meet S M B
  let I : Proper S := common S A B
  apply (old J).hom_ext
  intro e he
  have heTB : e ∈ TB.val := commonMask_right_subset S M A B he
  have heI : e ∈ I.val := Finset.inter_subset_right he
  change
    (L TB B Finset.inter_subset_right).incl
      ((L J TB (commonMask_right_subset S M A B)).incl ((old J).edge e)) =
    (L I B Finset.inter_subset_right).incl
      ((L J I Finset.inter_subset_right).incl ((old J).edge e))
  rw [(L J TB (commonMask_right_subset S M A B)).incl_edge e he,
    (L TB B Finset.inter_subset_right).incl_edge e heTB,
    (L J I Finset.inter_subset_right).incl_edge e he,
    (L I B Finset.inter_subset_right).incl_edge e heI]

/-- The precise noncommutative translated interface identity
inside the literal earlier two-block Link pushout.

The chosen representative g and shift u only satisfy the defining
point equation g·incl(u)=h·i(k); this theorem promotes it to
all parameters in the common earlier triple-mask group. -/
theorem actualLink_normalized_boundary
    (M A B : Proper S) (g h : (old A).Carrier)
    (k : (old (common S A B)).Carrier)
    (shift : (old (Step.meet S M A)).Carrier)
    (hbase :
      g * (L (Step.meet S M A) A Finset.inter_subset_right).incl shift =
        h * left D S old L A B k)
    (t : (old (Step.meet S M (common S A B))).Carrier) :
    pushoutInl (attachLeft h (left D S old L A B))
      (right D S old L A B)
      (attachLeft_injective h (left D S old L A B)
        (left_injective D S old L A B))
      (right_injective D S old L A B)
      (g * (L (Step.meet S M A) A Finset.inter_subset_right).incl
        (shift * normalizedCommonLeft D S old L M A B t)) =
    pushoutInr (attachLeft h (left D S old L A B))
      (right D S old L A B)
      (attachLeft_injective h (left D S old L A B)
        (left_injective D S old L A B))
      (right_injective D S old L A B)
      ((right D S old L A B k) *
        (L (Step.meet S M B) B Finset.inter_subset_right).incl
          (normalizedCommonRight D S old L M A B t)) := by
  exact normalized_boundary_pushout
    (left D S old L A B) (right D S old L A B)
    (left_injective D S old L A B) (right_injective D S old L A B)
    (L (Step.meet S M A) A Finset.inter_subset_right).incl
    (L (Step.meet S M B) B Finset.inter_subset_right).incl
    (normalizedCommonInterface D S old L M A B)
    (normalizedCommonLeft D S old L M A B)
    (normalizedCommonRight D S old L M A B)
    (normalizedCommon_left_square D S old L M A B)
    (normalizedCommon_right_square D S old L M A B)
    g h k shift hbase t

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
