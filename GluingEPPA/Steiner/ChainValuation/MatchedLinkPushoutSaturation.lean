import GluingEPPA.Steiner.ChainValuation.MatchedLinkInterfaceMask
import GluingEPPA.Steiner.ChainValuation.RestrictedPushoutSaturation

/-!
# Actual Link-coset pieces form an M-saturated exact pushout image

The earlier Link family proves that the two selected subgroup cosets
have identical attaching parameter fibres. Their restrictions are
therefore a literal exact pushout. The checked Cayley reachability
criterion shows that both cosets are closed under genuine M-edges.

Applying exact restricted-pushout saturation to this concrete pair
proves that the full quotient cannot have an M-edge escaping the
selected union, even at a point represented in both blocks.
This is an actual-Link specialization, not a new local assumption.
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

/-- The literal union of the two genuine M-coset pieces in the
full earlier Link attachment. It is a subset of the exact quotient
of the two full Cayley blocks, not of an auxiliary replacement. -/
def matchedLinkCosetCovered
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier) :
    Set (SetPushout
      (attachLeft h (left D S old L A B))
      (right D S old L A B)
      (attachLeft_injective h (left D S old L A B)
        (left_injective D S old L A B))
      (right_injective D S old L A B)) :=
  (matchedLinkCosetRestriction D S old L M A B h k).Covered
    (attachLeft_injective h (left D S old L A B)
      (left_injective D S old L A B))
    (right_injective D S old L A B)

/-- Each actual M-labelled edge starting in the union of the
two matched Cayley cosets remains in that union. Both sides
use the true named Cayley matchings and the literal quotient. -/
theorem matchedLinkCosetCovered_mask_closed
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier)
    (letter : E) (he : letter ∈ M.val)
    (p q : SetPushout
      (attachLeft h (left D S old L A B))
      (right D S old L A B)
      (attachLeft_injective h (left D S old L A B)
        (left_injective D S old L A B))
      (right_injective D S old L A B))
    (hp : p ∈ matchedLinkCosetCovered D S old L M A B h k)
    (hpq : MatchedRestriction.quotientEdges
      (fun e => ((block S old A).matching e).Rel)
      (fun e => ((block S old B).matching e).Rel)
      (attachLeft h (left D S old L A B))
      (right D S old L A B)
      (attachLeft_injective h (left D S old L A B)
        (left_injective D S old L A B))
      (right_injective D S old L A B)
      letter p q) :
    q ∈ matchedLinkCosetCovered D S old L M A B h k := by
  let R := matchedLinkCosetRestriction D S old L M A B h k
  have hleft :
      ∀ (e : E), e ∈ M.val →
        ∀ (x y : (old A).Carrier),
          ((block S old A).matching e).Rel x y →
          x ∈ R.left → y ∈ R.left := by
    intro e he x y hxy hx
    exact matchedLinkCoset_left_edge_closed
      D S old L M A B h k e he x y hxy hx
  have hright :
      ∀ (e : E), e ∈ M.val →
        ∀ (x y : (old B).Carrier),
          ((block S old B).matching e).Rel x y →
          x ∈ R.right → y ∈ R.right := by
    intro e he x y hxy hx
    exact matchedLinkCoset_right_edge_closed
      D S old L M A B h k e he x y hxy hx
  exact R.covered_closed_under_mask
    (attachLeft_injective h (left D S old L A B)
      (left_injective D S old L A B))
    (right_injective D S old L A B)
    M.val
    (fun e => ((block S old A).matching e).Rel)
    (fun e => ((block S old B).matching e).Rel)
    hleft hright letter he p q hp hpq

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
