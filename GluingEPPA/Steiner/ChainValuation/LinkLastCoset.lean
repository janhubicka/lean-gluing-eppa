import GluingEPPA.Steiner.ChainValuation.LastCosetStep
import GluingEPPA.Steiner.ChainValuation.LinkCayleyMask
import GluingEPPA.Steiner.ChainValuation.LinkRestrictedMatching

/-!
# The last-coset step for the actual earlier recursive Links

This specializes the checked generic last-block induction to the literal
groups `old A`, `old B` and the earlier Link maps along A ∩ B.
The coset description of a single block uses its true generator record,
not an abstract substitute group.

The theorem is a one-attachment induction step; the `BuildResult`
and `buildNonempty` induction and the smaller-chain equivariant
normal form remain distinct obligations.
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

/-- The actual old subgroup visible on mask M inside an earlier block A. -/
def restrictedSubgroup (M A : Proper S) : Subgroup (old A).Carrier :=
  (L (Step.meet S M A) A Finset.inter_subset_right).incl.range

/-- The two sides of an actual earlier Link attachment have equal pullbacks
of their restricted subgroups to the common attaching group. -/
theorem restrictedSubgroup_pullback (M A B : Proper S) :
    (restrictedSubgroup D S old L M A).comap (left D S old L A B) =
      (restrictedSubgroup D S old L M B).comap (right D S old L A B) := by
  exact mask_pullbacks_agree D S old L M A B

/-- Explicitly instantiate the generic one-attachment coset induction for
the genuine previously constructed Link family. -/
theorem link_extend_lastCoset
    (M A B : Proper S)
    (C : GluingEPPA.Steiner.ChainValuation.ChainState E (block S old A))
    (h : (old A).Carrier)
    (hsep : Disjoint C.entry
      (GluingEPPA.Steiner.ChainValuation.exitSet (block S old A) h
        (left D S old L A B)))
    (hprev :
      GluingEPPA.Steiner.ChainValuation.LastBlockCosetInvariant
        (block S old A) C M.val (restrictedSubgroup D S old L M A)) :
    GluingEPPA.Steiner.ChainValuation.LastBlockCosetInvariant
      (block S old B)
      (GluingEPPA.Steiner.ChainValuation.extend
        (block S old A) (block S old B) C h
        (left D S old L A B) (right D S old L A B)
        (left_injective D S old L A B)
        (right_injective D S old L A B)
        hsep (fun e heA heB => shared_edge D S old L A B e heA heB))
      M.val (restrictedSubgroup D S old L M B) := by
  apply GluingEPPA.Steiner.ChainValuation.extend_lastBlockCosetInvariant
    (block S old A) (block S old B) C h
    (left D S old L A B) (right D S old L A B)
    (left_injective D S old L A B)
    (right_injective D S old L A B)
    hsep (fun e heA heB => shared_edge D S old L A B e heA heB)
    M.val (restrictedSubgroup D S old L M A)
    (restrictedSubgroup D S old L M B)
  · exact restrictedSubgroup_pullback D S old L M A B
  · exact hprev
  · intro x y
    exact restricted_block_reach_iff_coset D S old L M B x y

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
