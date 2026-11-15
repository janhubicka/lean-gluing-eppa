import GluingEPPA.Steiner.ChainValuation.CoveredNamedAlignedHistory

/-!
# Positional internal boundaries of an active historical block interval

The actual M-component support interval consists of consecutive
historical named Cayley BLOCK OCCURRENCES, not just their source
mask labels. The original aligned Link boundary list has exactly
one boundary between each consecutive pair of these blocks.

This file proves the precise finite list fact needed to select
those *internal* boundary records without dropping an endpoint or
collapsing repeated masks. For an interval decomposition

    named blocks = front ++ active ++ back,

the internal boundary sublist begins after front.length original
boundaries and has exactly active.length - 1 entries. Its ordered
source-block endpoint pairs are precisely the consecutive pairs
of the active block interval.

The result is independent of any component-dependent choice of
attaching parameters. The next step combines it with genuine
active-boundary reachability and the unique shift/separation lemmas.
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

/-- Dropping one original boundary for each block in a preceding
non-active prefix leaves exactly the adjacent pairs of the
remaining nonempty block suffix. -/
theorem namedAdjacentBlockPairs_drop_prefix
    {M : Proper S} {R : BuildResult D S old L}
    (front tail : List (NamedHistoricalBlock D S old L M R))
    (hne : tail ≠ []) :
    (namedAdjacentBlockPairs D S old L (front ++ tail)).drop
      front.length =
    namedAdjacentBlockPairs D S old L tail := by
  induction front with
  | nil =>
      rfl
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases tail with
          | nil => exact False.elim (hne rfl)
          | cons y ys => rfl
      | cons y ys =>
          simpa only [List.cons_append, List.length_cons,
            namedAdjacentBlockPairs, List.drop_succ_cons]
            using ih

/-- The first active.length-1 adjacent pairs of a list beginning
with a nonempty active block interval are exactly the internal
adjacent pairs of that interval, regardless of the following suffix. -/
theorem namedAdjacentBlockPairs_take_active
    {M : Proper S} {R : BuildResult D S old L}
    (active back : List (NamedHistoricalBlock D S old L M R))
    (hne : active ≠ []) :
    (namedAdjacentBlockPairs D S old L (active ++ back)).take
      (active.length - 1) =
    namedAdjacentBlockPairs D S old L active := by
  induction active with
  | nil =>
      exact False.elim (hne rfl)
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [namedAdjacentBlockPairs]
      | cons b bs =>
          have htail : (b :: bs : List
              (NamedHistoricalBlock D S old L M R)) ≠ [] := by
            simp
          simpa [namedAdjacentBlockPairs, List.take_succ_cons]
            using ih htail

/-- An arbitrary nonempty active named-block interval has its
internal adjacent pairs exactly at the original boundary positions
front.length, ..., front.length + active.length - 2. -/
theorem namedAdjacentBlockPairs_internal_interval
    {M : Proper S} {R : BuildResult D S old L}
    (front active back :
      List (NamedHistoricalBlock D S old L M R))
    (hne : active ≠ []) :
    ((namedAdjacentBlockPairs D S old L
      (front ++ active ++ back)).drop front.length).take
        (active.length - 1) =
      namedAdjacentBlockPairs D S old L active := by
  have htail : active ++ back ≠ [] := by
    intro he
    apply hne
    exact (List.append_eq_nil_iff.mp he).1
  have hdrop := namedAdjacentBlockPairs_drop_prefix
    D S old L front (active ++ back) htail
  simpa only [List.append_assoc, hdrop] using
    namedAdjacentBlockPairs_take_active
      D S old L active back hne

/-- Positional selection from a TRUE ordered list of historical
Link boundary records recovers precisely the internal boundaries
of an active named Cayley-block interval.

No mask distinctness is assumed: repeated source masks still
occupy separate positions. Linkedness identifies the true middle
named chart shared by each consecutive original boundary pair. -/
theorem alignedBoundaryList_active_internal_pairs
    {M : Proper S} {R : BuildResult D S old L}
    (last : NamedHistoricalBlock D S old L M R)
    (boundaries : List (AlignedNamedBoundary D S old L M R))
    (hlinked : AlignedBoundaryList.Linked D S old L boundaries)
    (front active back :
      List (NamedHistoricalBlock D S old L M R))
    (hne : active ≠ [])
    (hblocks : alignedBoundaryBlockSequence D S old L
        last boundaries = front ++ active ++ back) :
    ((boundaries.drop front.length).take
      (active.length - 1)).map
        (fun P => (P.leftNamed, P.rightNamed)) =
      namedAdjacentBlockPairs D S old L active := by
  have hboundary := alignedBoundaryBlockSequence_pairs
    D S old L last boundaries hlinked
  rw [hblocks] at hboundary
  calc
    ((boundaries.drop front.length).take
      (active.length - 1)).map
        (fun P => (P.leftNamed, P.rightNamed)) =
      ((boundaries.map
        (fun P => (P.leftNamed, P.rightNamed))).drop front.length).take
          (active.length - 1) := by
            simp only [List.map_take, List.map_drop]
    _ = ((namedAdjacentBlockPairs D S old L
        (front ++ active ++ back)).drop front.length).take
        (active.length - 1) := by rw [hboundary]
    _ = namedAdjacentBlockPairs D S old L active :=
      namedAdjacentBlockPairs_internal_interval
        D S old L front active back hne

/-- The positional internal-boundary theorem is available on the
SAME original covered named history used to extract the actual
M-component active interval. Its only additional geometric input
is the already separately established linkedness of historical
boundary charts; no new boundary point or group coordinate is
assumed in this finite list calculation. -/
theorem CoveredNamedAlignedHistory.internal_boundary_pairs
    {M : Proper S}
    (H : CoveredNamedAlignedHistory D S old L M)
    (hlinked : AlignedBoundaryList.Linked D S old L H.aligned)
    (front active back :
      List (NamedHistoricalBlock D S old L M H.named.data.chain))
    (hdecomp : H.named.named = front ++ active ++ back)
    (hne : active ≠ []) :
    ((H.aligned.drop front.length).take
      (active.length - 1)).map
        (fun P => (P.leftNamed, P.rightNamed)) =
      namedAdjacentBlockPairs D S old L active := by
  exact alignedBoundaryList_active_internal_pairs
    D S old L
    (namedHistoricalLast D S old L M
      H.named.data.chain H.named.data.lastInv)
    H.aligned hlinked front active back hne
    (H.blocksAgree.symm.trans hdecomp)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
