import GluingEPPA.Steiner.ChainValuation.ActualNormalizedTripleSeparation
import GluingEPPA.Steiner.ChainValuation.LinkCayleyMask

/-!
# One-shift normalization of an interior historical Link block

At an interior block K_A of the genuine earlier Link chain, suppose
the incoming attachment parameter kIn and the outgoing attachment
parameter kOut select two points connected by M-coloured Cayley
edges inside K_A. The entire M-component of those points is one
left coset of the actual included group K_(M∩A).

Normalize the block's origin at the *incoming attachment point*.
Its incoming shift is exactly 1. The path to the outgoing point
produces one outgoing shift u∈K_(M∩A).

The verified noncommutative normalized triple-interface theorem
then proves the complete normalized incoming and outgoing
K_(M∩Aprev∩A) and K_(M∩A∩Anext) cosets are disjoint whenever
the original triple is separated. No independent choice of two
shifts or unjustified Proper M assertion is needed.

This is the one-block geometric induction step; producing a
compatible sequence of kIn/kOut witnesses across all active blocks
is a separate finite-history task.
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

/-- From an M-path between the actual incoming and outgoing
attachment points of one historical Cayley block, construct its
normalized outgoing shift in K_(M∩A), with no new assumption. -/
theorem normalizedInterior_outgoingShift_exists
    (M : Proper S) (x y z : Atom S old)
    (kIn : (old (common S x.1 y.1)).Carrier)
    (kOut : (old (common S y.1 z.1)).Carrier)
    (hpath :
      LabelReach (fun e => ((block S old y.1).matching e).Rel)
        M.val
        (right D S old L x.1 y.1 kIn)
        (y.2 * left D S old L y.1 z.1 kOut)) :
    ∃ shift : (old (Step.meet S M y.1)).Carrier,
      (right D S old L x.1 y.1 kIn) *
        (L (Step.meet S M y.1) y.1
          Finset.inter_subset_right).incl shift =
      y.2 * left D S old L y.1 z.1 kOut := by
  let g := right D S old L x.1 y.1 kIn
  let target := y.2 * left D S old L y.1 z.1 kOut
  let p := (L (Step.meet S M y.1) y.1
    Finset.inter_subset_right).incl
  have hcoset :
      target ∈ leftCoset
        (restrictedSubgroup D S old L M y.1) g :=
    (restricted_block_reach_iff_coset
      D S old L M y.1 g target).mp hpath
  change g⁻¹ * target ∈ p.range at hcoset
  obtain ⟨shift, hshift⟩ := hcoset
  refine ⟨shift, ?_⟩
  change g * p shift = target
  calc
    g * p shift = g * (g⁻¹ * target) := by rw [hshift]
    _ = target := by group

/-- The normalized middle block has its incoming shift equal to 1,
and the outgoing shift supplied by the actual M-path. The *whole*
normalized incoming and outgoing interface cosets are disjoint. -/
theorem normalizedInterior_separated_of_M_path
    (M : Proper S) (x y z : Atom S old)
    (kIn : (old (common S x.1 y.1)).Carrier)
    (kOut : (old (common S y.1 z.1)).Carrier)
    (hpath :
      LabelReach (fun e => ((block S old y.1).matching e).Rel)
        M.val
        (right D S old L x.1 y.1 kIn)
        (y.2 * left D S old L y.1 z.1 kOut))
    (hsep : tripleSeparated D S old L x y z) :
    ∃ shift : (old (Step.meet S M y.1)).Carrier,
      (right D S old L x.1 y.1 kIn) *
        (L (Step.meet S M y.1) y.1
          Finset.inter_subset_right).incl shift =
          y.2 * left D S old L y.1 z.1 kOut ∧
      Disjoint
        (leftCoset
          (normalizedCommonRight D S old L M x.1 y.1).range 1)
        (leftCoset
          (normalizedCommonLeft D S old L M y.1 z.1).range shift) := by
  obtain ⟨shift, hshift⟩ :=
    normalizedInterior_outgoingShift_exists
      D S old L M x y z kIn kOut hpath
  refine ⟨shift, hshift, ?_⟩
  let g := right D S old L x.1 y.1 kIn
  let p := (L (Step.meet S M y.1) y.1
    Finset.inter_subset_right).incl
  have hIn : g * p 1 = right D S old L x.1 y.1 kIn := by
    simp [g]
  exact actual_normalizedTripleSeparated
    D S old L M x y z g kIn kOut 1 shift
    hIn hshift hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
