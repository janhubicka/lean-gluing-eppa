import GluingEPPA.Steiner.ChainValuation.RestrictedComponentMatching
import GluingEPPA.Steiner.ChainValuation.MatchingGluing

/-!
# Every actual restricted-component attachment is witnessed precisely

The previous development constructs the matching between genuine
M-reachability quotient classes by pulling back the actual Link
matching between their left cosets.

We check the two directions required by MatchingGluing: each
literal attaching element joins its old and new component classes,
and every such matching edge has a genuine attaching parameter.
This is not an existence axiom or a replacement matching.
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

/-- A genuine M-component class evaluates to precisely the left coset
of any representative, without a choice of representative class. -/
theorem componentCosetMap_mk
    (M A : Proper S) (x : (old A).Carrier) :
    componentCosetMap D S old L M A
      (Quotient.mk
        (labelReachSetoid (fun e => ((block S old A).matching e).Rel) M.val) x) =
      leftCoset
        (L (Step.meet S M A) A Finset.inter_subset_right).incl.range x := by
  rfl

/-- Every literal attaching point determines a matching edge between
its two actual M-component quotient classes. -/
theorem restrictedActualComponentMatching_attach
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier) :
    (restrictedActualComponentMatching D S old L M A B h).Rel
      (.inl (Quotient.mk
        (labelReachSetoid (fun e => ((block S old A).matching e).Rel) M.val)
        (h * left D S old L A B k)))
      (.inr (Quotient.mk
        (labelReachSetoid (fun e => ((block S old B).matching e).Rel) M.val)
        (right D S old L A B k))) := by
  change (restrictedLinkMatching D S old L M A B h).Rel
    (.inl (leftCoset
      (L (Step.meet S M A) A Finset.inter_subset_right).incl.range
      (h * left D S old L A B k)))
    (.inr (leftCoset
      (L (Step.meet S M B) B Finset.inter_subset_right).incl.range
      (right D S old L A B k)))
  exact ⟨k, rfl, rfl⟩

/-- Conversely, every matching edge between actual restricted component
classes is an attachment witnessed by a point of the real common
earlier group K_(A∩B). This is the exact completeness premise of the
generic glued-component classification. -/
theorem restrictedActualComponentMatching_complete
    (M A B : Proper S) (h : (old A).Carrier) :
    MatchesAttachment
      (labelReachSetoid (fun e => ((block S old A).matching e).Rel) M.val)
      (labelReachSetoid (fun e => ((block S old B).matching e).Rel) M.val)
      (fun k : (old (common S A B)).Carrier =>
        h * left D S old L A B k)
      (right D S old L A B)
      (restrictedActualComponentMatching D S old L M A B h) := by
  intro x y hrel
  change (restrictedLinkMatching D S old L M A B h).Rel
    (.inl (componentCosetMap D S old L M A x))
    (.inr (componentCosetMap D S old L M B y)) at hrel
  obtain ⟨k, hOld, hNew⟩ := hrel
  refine ⟨k, ?_, ?_⟩
  · apply componentCosetMap_injective D S old L M A
    rw [componentCosetMap_mk D S old L M A]
    exact hOld.symm
  · apply componentCosetMap_injective D S old L M B
    rw [componentCosetMap_mk D S old L M B]
    exact hNew.symm

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
