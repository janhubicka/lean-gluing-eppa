import GluingEPPA.Steiner.ChainValuation.ActualAttachmentWitness
import GluingEPPA.Steiner.ChainValuation.PushoutReachBridge
import GluingEPPA.Steiner.ChainValuation.GroupAttachment

/-!
# Exact two-block M-component classification

For two real earlier Cayley blocks K_A and K_B attached through
the real earlier Link maps on K_(A∩B), the M-coloured reachability
components of their literal injective set pushout are exactly the
classes of the canonical restricted-coset matching.

This is the two-block base case of global chain restriction.
No higher-acyclicity existence theorem, hypothetical K_S, or
undischarged matching hypothesis is invoked.
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

/-- The literal union of genuine named Cayley edges in a two-block
Link pushout has exactly the components given by the actual
quotient-coset partial matching. -/
theorem twoBlock_reach_iff_matching_class
    (M A B : Proper S) (h : (old A).Carrier)
    (a b : Sum (old A).Carrier (old B).Carrier) :
    LabelReach
      (pushoutLabelRel
        (fun e => ((block S old A).matching e).Rel)
        (fun e => ((block S old B).matching e).Rel)
        (attachLeft h (left D S old L A B))
        (right D S old L A B)
        (attachLeft_injective h (left D S old L A B)
          (left_injective D S old L A B))
        (right_injective D S old L A B))
      M.val
      (pushoutPoint
        (attachLeft h (left D S old L A B))
        (right D S old L A B)
        (attachLeft_injective h (left D S old L A B)
          (left_injective D S old L A B))
        (right_injective D S old L A B) a)
      (pushoutPoint
        (attachLeft h (left D S old L A B))
        (right D S old L A B)
        (attachLeft_injective h (left D S old L A B)
          (left_injective D S old L A B))
        (right_injective D S old L A B) b) ↔
    componentClass
        (labelReachSetoid
          (fun e => ((block S old A).matching e).Rel) M.val)
        (labelReachSetoid
          (fun e => ((block S old B).matching e).Rel) M.val)
        (restrictedActualComponentMatching D S old L M A B h) a =
    componentClass
        (labelReachSetoid
          (fun e => ((block S old A).matching e).Rel) M.val)
        (labelReachSetoid
          (fun e => ((block S old B).matching e).Rel) M.val)
        (restrictedActualComponentMatching D S old L M A B h) b := by
  apply pushoutReach_iff_matchingClass_eq
    (fun e => ((block S old A).matching e).Rel)
    (fun e => ((block S old B).matching e).Rel)
    M.val
    (attachLeft h (left D S old L A B))
    (right D S old L A B)
    (attachLeft_injective h (left D S old L A B)
      (left_injective D S old L A B))
    (right_injective D S old L A B)
    (restrictedActualComponentMatching D S old L M A B h)
  · intro k
    exact restrictedActualComponentMatching_attach D S old L M A B h k
  · intro x y hxy
    exact hxy
  · intro x y hxy
    exact hxy
  · exact restrictedActualComponentMatching_complete D S old L M A B h

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
