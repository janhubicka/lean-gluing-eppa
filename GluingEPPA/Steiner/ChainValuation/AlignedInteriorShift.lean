import GluingEPPA.Steiner.ChainValuation.AlignedNamedBoundaryComponentWitness
import GluingEPPA.Steiner.ChainValuation.HistoricalInternalPaths

/-!
# Unique normalized interior shift between adjacent historical interfaces

The proper-mask chain normalization requires the two successive
attachment parameters surrounding each occupied interior K_A block
to be comparable in the SAME historical Cayley coordinates.

If two aligned boundaries have literally the same named middle
block, and a chosen actual M-component reaches one parameter of
each interface, the endpoint representatives lie in the same
historical M-coset. The checked historical chart converts this
into a UNIQUE shift in the genuine earlier K_(M intersect A).

There is no simultaneous/coherence hypothesis on the chosen
interface points: the same-component condition alone forces
their displacement into K_(M intersect A). This is the
noncommutative shift equation required by the manuscript's
normalized chain, independently of all later recursion details.
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

/-- Actual consecutive interfaces meeting the SAME global
M-component determine a unique noncommutative normalized
middle-block shift in K_(M∩A).

The additional hMiddle hypothesis says they share the literal
named source-block chart, not just the same source alphabet.
This is satisfied by the original left-to-right LinkChain
history: later attachments transport this chart identically
on both adjacent records. -/
theorem AlignedNamedBoundary.adjacent_unique_interior_shift
    {M : Proper S} {R : BuildResult D S old L}
    (P Q : AlignedNamedBoundary D S old L M R)
    (hMiddle : P.rightNamed = Q.leftNamed)
    (q : R.state.Space)
    (k : (old (common S P.boundary.leftMask
      P.boundary.rightMask)).Carrier)
    (l : (old (common S Q.boundary.leftMask
      Q.boundary.rightMask)).Carrier)
    (hk : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (P.boundary.interfaceMap D S old L k))
    (hl : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (Q.boundary.interfaceMap D S old L l)) :
    ∃ x y : (old P.rightNamed.source).Carrier,
      P.rightNamed.chart.embed x =
        P.boundary.interfaceMap D S old L k ∧
      P.rightNamed.chart.embed y =
        Q.boundary.interfaceMap D S old L l ∧
      ∃! shift : (old (Step.meet S M P.rightNamed.source)).Carrier,
        x * (L (Step.meet S M P.rightNamed.source)
          P.rightNamed.source Finset.inter_subset_right).incl shift = y := by
  obtain ⟨x, hx⟩ :=
    (P.interface_has_named_endpoints D S old L k).2
  -- Transport the existential middle-coordinate statement first:
  -- rewriting after choosing y would give a dependent-carrier mismatch.
  have hRight : ∃ y : (old P.rightNamed.source).Carrier,
      P.rightNamed.chart.embed y =
        Q.boundary.interfaceMap D S old L l := by
    rw [hMiddle]
    exact (Q.interface_has_named_endpoints D S old L l).1
  obtain ⟨y, hy⟩ := hRight
  have hxReach : LabelReach
      (fun e => (R.state.matching e).Rel) M.val
      q (P.rightNamed.chart.embed x) := by
    rw [hx]
    exact hk
  have hyReach : LabelReach
      (fun e => (R.state.matching e).Rel) M.val
      q (P.rightNamed.chart.embed y) := by
    rw [hy]
    exact hl
  have hxy : LabelReach
      (fun e => (R.state.matching e).Rel) M.val
      (P.rightNamed.chart.embed x)
      (P.rightNamed.chart.embed y) :=
    LabelReach.trans (LabelReach.symm hxReach) hyReach
  refine ⟨x, y, hx, hy, ?_⟩
  exact historical_chart_unique_displacement
    D S old L M P.rightNamed.source R.current.1
    R.state P.rightNamed.chart x y hxy

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
