import GluingEPPA.Steiner.ChainValuation.MatchedLinkCosetRestriction
import GluingEPPA.Steiner.ChainValuation.LinkCayleyMask

/-!
# Actual Link restricted cosets are closed under genuine M-edges

The selected pieces of a matched Link attachment are the literal
left cosets of K_(M ∩ A) and K_(M ∩ B). Rather than replaying
noncommutative calculations, use the verified theorem that these
cosets are exactly the connected components of the true Cayley
M-edge relation. One additional M-edge must remain in the same coset.

These lemmas discharge local saturation requirements without
introducing a new group or assuming anything about K_S.
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

/-- Every actual masked Cayley edge remains in a left coset of the
earlier subgroup K_(M∩A). This is a consequence of the exact
masked-reachability/coset equivalence, not a separate group axiom. -/
theorem restrictedBlockCoset_edge_closed
    (M A : Proper S) (base x y : (old A).Carrier)
    (letter : E) (he : letter ∈ M.val)
    (hxy : ((block S old A).matching letter).Rel x y)
    (hx : x ∈ leftCoset
      (L (Step.meet S M A) A Finset.inter_subset_right).incl.range base) :
    y ∈ leftCoset
      (L (Step.meet S M A) A Finset.inter_subset_right).incl.range base := by
  have hgx : LabelReach
      (fun e => ((block S old A).matching e).Rel) M.val base x :=
    (restricted_block_reach_iff_coset D S old L M A base x).mpr hx
  have hxy' : LabelReach
      (fun e => ((block S old A).matching e).Rel) M.val x y :=
    LabelReach.edge letter he hxy
  exact (restricted_block_reach_iff_coset D S old L M A base y).mp
    (LabelReach.trans hgx hxy')

/-- The old-side piece of a literal matched Link attachment is
closed under every genuine M-labelled Cayley transition. -/
theorem matchedLinkCoset_left_edge_closed
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier)
    (letter : E) (he : letter ∈ M.val)
    (x y : (old A).Carrier)
    (hxy : ((block S old A).matching letter).Rel x y)
    (hx : x ∈ (matchedLinkCosetRestriction D S old L M A B h k).left) :
    y ∈ (matchedLinkCosetRestriction D S old L M A B h k).left := by
  exact restrictedBlockCoset_edge_closed D S old L M A
    (h * left D S old L A B k) x y letter he hxy hx

/-- Symmetrically, the new-side piece is closed under every genuine
M-labelled Cayley transition, including the exact shared attachment. -/
theorem matchedLinkCoset_right_edge_closed
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier)
    (letter : E) (he : letter ∈ M.val)
    (x y : (old B).Carrier)
    (hxy : ((block S old B).matching letter).Rel x y)
    (hx : x ∈ (matchedLinkCosetRestriction D S old L M A B h k).right) :
    y ∈ (matchedLinkCosetRestriction D S old L M A B h k).right := by
  exact restrictedBlockCoset_edge_closed D S old L M B
    (right D S old L A B k) x y letter he hxy hx

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
