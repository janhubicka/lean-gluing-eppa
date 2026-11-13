import GluingEPPA.Steiner.ChainValuation.HistoricalInternalPaths
import GluingEPPA.Steiner.ChainValuation.ActualNormalizedTripleSeparation

/-!
# Genuine interior normalization from a single M-component

At an interior atom y of an actual separated Link chain, take the
incoming and outgoing points determined by genuine adjacent attaching
parameters. If both are reachable from the same point q in the *final*
M-component, and a historical chart for y is available, the checked
reachability reflection puts their connecting path inside the actual
earlier Cayley group K_y.

This gives the unique outgoing shift in K_(M ∩ y); the incoming shift
is the identity. The full normalized incoming and outgoing interface
cosets are disjoint by the original triple separation. In particular,
their separation is not an extra hypothesis on the normalized chain.

The historical chart and the two component-reachability witnesses are
explicit inputs. This module does not yet construct a coherent family
of such data for every interior atom of every M-component.
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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- The incoming and outgoing *actual attaching points* of an interior
block are M-connected inside that original block, provided their
historical images lie in the same final M-component. -/
theorem historicalInterior_blockPath_of_component
    (M : Proper S) (x y z : Atom S old)
    (B : Proper S) (C : ChainState E (block S old B))
    (T : HistoricalCosetChart (block S old B) C M.val
      (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl.range)
    (q : C.Space)
    (kIn : (old (common S x.1 y.1)).Carrier)
    (kOut : (old (common S y.1 z.1)).Carrier)
    (hIn : LabelReach (fun e => (C.matching e).Rel) M.val
      q (T.embed (right D S old L x.1 y.1 kIn)))
    (hOut : LabelReach (fun e => (C.matching e).Rel) M.val
      q (T.embed (y.2 * left D S old L y.1 z.1 kOut))) :
    LabelReach (fun e => ((block S old y.1).matching e).Rel) M.val
      (right D S old L x.1 y.1 kIn)
      (y.2 * left D S old L y.1 z.1 kOut) := by
  exact historical_chart_common_component_has_internal_path
    D S old L M y.1 B C T q
    (right D S old L x.1 y.1 kIn)
    (y.2 * left D S old L y.1 z.1 kOut)
    hIn hOut

/-- The actual component witnesses determine a *unique* shift of the
middle K_(M ∩ y) block. Using identity as incoming shift, the entire
normalized entry/exit cosets are disjoint. The displacement equation
is in the noncommutative order of the actual Link inclusions. -/
theorem historicalInterior_unique_shift_and_separation
    (M : Proper S) (x y z : Atom S old)
    (B : Proper S) (C : ChainState E (block S old B))
    (T : HistoricalCosetChart (block S old B) C M.val
      (L (Step.meet S M y.1) y.1 Finset.inter_subset_right).incl.range)
    (q : C.Space)
    (kIn : (old (common S x.1 y.1)).Carrier)
    (kOut : (old (common S y.1 z.1)).Carrier)
    (hIn : LabelReach (fun e => (C.matching e).Rel) M.val
      q (T.embed (right D S old L x.1 y.1 kIn)))
    (hOut : LabelReach (fun e => (C.matching e).Rel) M.val
      q (T.embed (y.2 * left D S old L y.1 z.1 kOut)))
    (hsep : tripleSeparated D S old L x y z) :
    ∃! shift : (old (Step.meet S M y.1)).Carrier,
      (right D S old L x.1 y.1 kIn) *
        (L (Step.meet S M y.1) y.1
          Finset.inter_subset_right).incl shift =
          y.2 * left D S old L y.1 z.1 kOut ∧
      Disjoint
        (leftCoset
          (normalizedCommonRight D S old L M x.1 y.1).range 1)
        (leftCoset
          (normalizedCommonLeft D S old L M y.1 z.1).range shift) := by
  have hxy : LabelReach (fun e => (C.matching e).Rel) M.val
      (T.embed (right D S old L x.1 y.1 kIn))
      (T.embed (y.2 * left D S old L y.1 z.1 kOut)) :=
    LabelReach.trans (LabelReach.symm hIn) hOut
  obtain ⟨shift, hshift, hunique⟩ :=
    historical_chart_unique_displacement D S old L
      M y.1 B C T
      (right D S old L x.1 y.1 kIn)
      (y.2 * left D S old L y.1 z.1 kOut) hxy
  refine ⟨shift, ⟨hshift, ?_⟩, ?_⟩
  · have hfirst :
        (right D S old L x.1 y.1 kIn) *
          (L (Step.meet S M y.1) y.1
            Finset.inter_subset_right).incl 1 =
            right D S old L x.1 y.1 kIn := by simp
    exact actual_normalizedTripleSeparated
      D S old L M x y z
      (right D S old L x.1 y.1 kIn)
      kIn kOut 1 shift hfirst hshift hsep
  · intro shift' hshift'
    exact hunique shift' hshift'.1

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
