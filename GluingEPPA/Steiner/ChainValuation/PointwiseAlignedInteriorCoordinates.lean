import GluingEPPA.Steiner.ChainValuation.CombinedHistoricalExactCharts
import GluingEPPA.Steiner.ChainValuation.LinkedAlignedBoundaryPairs
import GluingEPPA.Steiner.ChainValuation.HistoricalInternalPaths

/-!
# Literal original coordinates of adjacent historical interface points

An equality of the *ranges* of historical and named Cayley charts
does not determine the coordinates of particular interface points.
The pointwise historical-boundary theorem does determine them, via
canonical casts of equal source-mask indices. This module makes
that identification explicit on both sides of each true boundary.

For two adjacent boundaries with the SAME named middle-block
chart, two interface points reached by one genuine M-component
then determine a UNIQUE displacement in the actual previous
stage K_(M intersect A). The incoming and outgoing endpoints in
the displacement equation are the original attachment coordinates,
not arbitrary witnesses chosen from their image sets.

The full normalized triple-separation calculation still needs
to identify these coordinates with the actual three-atom shifts
of the original LinkChain.
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

/-- The actual left-group coordinate of a genuine interface
parameter in its named original historical Cayley block. -/
def AlignedNamedBoundary.leftNamedCoordinate
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (k : (old (common S P.boundary.leftMask
      P.boundary.rightMask)).Carrier) :
    (old P.leftNamed.source).Carrier :=
  sourceMaskCast S old P.agree.1 (P.boundary.leftParam k)

/-- The actual right-group coordinate of the same interface
parameter in its named historical Cayley block. -/
def AlignedNamedBoundary.rightNamedCoordinate
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (k : (old (common S P.boundary.leftMask
      P.boundary.rightMask)).Carrier) :
    (old P.rightNamed.source).Carrier :=
  sourceMaskCast S old P.agree.2.1 (P.boundary.rightParam k)

/-- Pointwise alignment identifies the LEFT named coordinate,
not just its image set, with the genuine original interface point. -/
theorem AlignedNamedBoundary.leftCoordinate_image
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (hpoint : P.boundary.PointwiseNamed D S old L
      P.leftNamed P.rightNamed P.agree)
    (k : (old (common S P.boundary.leftMask
      P.boundary.rightMask)).Carrier) :
    P.leftNamed.chart.embed (P.leftNamedCoordinate D S old L k) =
      P.boundary.interfaceMap D S old L k := by
  exact (hpoint.1 (P.boundary.leftParam k)).symm

/-- The same equality for the genuine RIGHT named coordinate. -/
theorem AlignedNamedBoundary.rightCoordinate_image
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (hpoint : P.boundary.PointwiseNamed D S old L
      P.leftNamed P.rightNamed P.agree)
    (k : (old (common S P.boundary.leftMask
      P.boundary.rightMask)).Carrier) :
    P.rightNamed.chart.embed (P.rightNamedCoordinate D S old L k) =
      P.boundary.interfaceMap D S old L k := by
  exact (hpoint.2 (P.boundary.rightParam k)).symm.trans
    (P.boundary.interfaceMap_eq_right D S old L k).symm

/-- Transport a coordinate of a named source group along LITERAL
equality of named historical blocks. No arbitrary isomorphism of
group carriers is chosen. -/
theorem namedChart_apply_cast_of_eq
    {M : Proper S} {R : BuildResult D S old L}
    (T U : NamedHistoricalBlock D S old L M R)
    (h : T = U) (x : (old U.source).Carrier) :
    T.chart.embed
      (sourceMaskCast S old
        (congrArg
          (fun W : NamedHistoricalBlock D S old L M R => W.source) h).symm
        x) = U.chart.embed x := by
  cases h
  rfl

/-- Exact equation for the unique normalized interior shift, with
BOTH endpoints fixed as the actual source-Cayley coordinates of
the two given historical interface parameters.

The equality of the dependent middle-block charts is explicit.
On any original finite separated chain, it is supplied by the
verified consecutive-boundary theorem. -/
theorem AlignedNamedBoundary.adjacent_exact_coordinate_shift
    {M : Proper S} {R : BuildResult D S old L}
    (P Q : AlignedNamedBoundary D S old L M R)
    (hMiddle : P.rightNamed = Q.leftNamed)
    (hpointP : P.boundary.PointwiseNamed D S old L
      P.leftNamed P.rightNamed P.agree)
    (hpointQ : Q.boundary.PointwiseNamed D S old L
      Q.leftNamed Q.rightNamed Q.agree)
    (q : R.state.Space)
    (k : (old (common S P.boundary.leftMask
      P.boundary.rightMask)).Carrier)
    (l : (old (common S Q.boundary.leftMask
      Q.boundary.rightMask)).Carrier)
    (hk : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (P.boundary.interfaceMap D S old L k))
    (hl : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (Q.boundary.interfaceMap D S old L l)) :
    let x := P.rightNamedCoordinate D S old L k
    let y := sourceMaskCast S old
      (congrArg (fun W : NamedHistoricalBlock D S old L M R =>
        W.source) hMiddle).symm
      (Q.leftNamedCoordinate D S old L l)
    ∃! shift : (old (Step.meet S M P.rightNamed.source)).Carrier,
      x * (L (Step.meet S M P.rightNamed.source)
        P.rightNamed.source Finset.inter_subset_right).incl shift = y := by
  let x := P.rightNamedCoordinate D S old L k
  let y := sourceMaskCast S old
    (congrArg (fun W : NamedHistoricalBlock D S old L M R =>
      W.source) hMiddle).symm
    (Q.leftNamedCoordinate D S old L l)
  have hx : P.rightNamed.chart.embed x =
      P.boundary.interfaceMap D S old L k :=
    P.rightCoordinate_image D S old L hpointP k
  have hy : P.rightNamed.chart.embed y =
      Q.boundary.interfaceMap D S old L l := by
    calc
      P.rightNamed.chart.embed y =
          Q.leftNamed.chart.embed
            (Q.leftNamedCoordinate D S old L l) :=
        namedChart_apply_cast_of_eq D S old L
          P.rightNamed Q.leftNamed hMiddle
          (Q.leftNamedCoordinate D S old L l)
      _ = Q.boundary.interfaceMap D S old L l :=
        Q.leftCoordinate_image D S old L hpointQ l
  have hreach :
      LabelReach (fun e => (R.state.matching e).Rel) M.val
        (P.rightNamed.chart.embed x)
        (P.rightNamed.chart.embed y) := by
    have hqx : LabelReach (fun e => (R.state.matching e).Rel)
        M.val q (P.rightNamed.chart.embed x) := by
      rw [hx]
      exact hk
    have hqy : LabelReach (fun e => (R.state.matching e).Rel)
        M.val q (P.rightNamed.chart.embed y) := by
      rw [hy]
      exact hl
    exact LabelReach.trans (LabelReach.symm hqx) hqy
  change ∃! shift : (old (Step.meet S M P.rightNamed.source)).Carrier,
    x * (L (Step.meet S M P.rightNamed.source)
      P.rightNamed.source Finset.inter_subset_right).incl shift = y
  exact historical_chart_unique_displacement
    D S old L M P.rightNamed.source R.current.1
    R.state P.rightNamed.chart x y hreach

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
