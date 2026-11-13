import GluingEPPA.Steiner.ChainValuation.HistoricalCosetCharts
import GluingEPPA.Steiner.ChainValuation.LinkCayleyMask

/-!
# Internal paths and displacements in an actual historical Cayley block

A historical chart already reflects the ambient M-component equivalence as
cosets of the actual earlier Link range. The Cayley reachability theorem
then reflects ambient connectivity into a path inside that original block.
It also recovers the unique element of K_(M ∩ A) translating one endpoint
to the other. These are the internal-path and left-shift facts needed when
normalizing consecutive interfaces in Part II.

The chart remains an explicit input. This file does not assert that all
chosen consecutive boundary charts have yet been aligned with the finite
history, or that the entire normalized component has been assembled.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- Ambient connectivity between points of one actual historical block is
exactly connectivity within the block using the same retained letters. -/
theorem historical_chart_reach_iff_block_reach
    (M A B : Proper S) (C : ChainState E (block S old B))
    (T : HistoricalCosetChart (block S old B) C M.val
      (L (Step.meet S M A) A Finset.inter_subset_right).incl.range)
    (x y : (old A).Carrier) :
    LabelReach (fun e => (C.matching e).Rel) M.val (T.embed x) (T.embed y) ↔
      LabelReach (fun e => ((block S old A).matching e).Rel) M.val x y := by
  exact (T.reach_iff x y).trans
    (restricted_block_reach_iff_coset D S old L M A x y).symm

/-- Incoming and outgoing representatives lying in the same ambient
component are connected inside their common historical source block.
No path outside that block is used in the conclusion. -/
theorem historical_chart_common_component_has_internal_path
    (M A B : Proper S) (C : ChainState E (block S old B))
    (T : HistoricalCosetChart (block S old B) C M.val
      (L (Step.meet S M A) A Finset.inter_subset_right).incl.range)
    (q : C.Space) (x y : (old A).Carrier)
    (hx : LabelReach (fun e => (C.matching e).Rel) M.val q (T.embed x))
    (hy : LabelReach (fun e => (C.matching e).Rel) M.val q (T.embed y)) :
    LabelReach (fun e => ((block S old A).matching e).Rel) M.val x y := by
  exact (historical_chart_reach_iff_block_reach
    D S old L M A B C T x y).mp
      (LabelReach.trans (LabelReach.symm hx) hy)

/-- The displacement uses the genuine previous-stage group K_(M ∩ A),
not a chosen abstract subgroup or an element of a hypothetical top group.
The equation has the left-translation order required by the manuscript. -/
theorem historical_chart_unique_displacement
    (M A B : Proper S) (C : ChainState E (block S old B))
    (T : HistoricalCosetChart (block S old B) C M.val
      (L (Step.meet S M A) A Finset.inter_subset_right).incl.range)
    (x y : (old A).Carrier)
    (hxy : LabelReach (fun e => (C.matching e).Rel) M.val
      (T.embed x) (T.embed y)) :
    ∃! u : (old (Step.meet S M A)).Carrier,
      x * (L (Step.meet S M A) A Finset.inter_subset_right).incl u = y := by
  have hcoset := (T.reach_iff x y).mp hxy
  change x⁻¹ * y ∈
    (L (Step.meet S M A) A Finset.inter_subset_right).incl.range at hcoset
  obtain ⟨u, hu⟩ := hcoset
  have hmul : x * (L (Step.meet S M A) A Finset.inter_subset_right).incl u = y := by
    calc
      x * (L (Step.meet S M A) A Finset.inter_subset_right).incl u =
          x * (x⁻¹ * y) := congrArg (fun z => x * z) hu
      _ = y := by group
  refine ⟨u, hmul, ?_⟩
  intro v hv
  apply Link.injective D (old (Step.meet S M A)) (old A)
    Finset.inter_subset_right
    (L (Step.meet S M A) A Finset.inter_subset_right)
  exact mul_left_cancel (hv.trans hmul.symm)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
