import GluingEPPA.Steiner.ChainValuation.ChosenInternalInterfaceShifts
import GluingEPPA.Steiner.ChainValuation.PointwiseCoveredNamedHistory
import GluingEPPA.Steiner.ChainValuation.PointwiseAlignedInteriorCoordinates

/-!
# Exact original coordinates of every selected active interior shift

For two successive genuine historical interface parameters of an
M-component, the earlier result supplies a unique displacement in
K_(M ∩ A). But for normalizing the original entry/exit attachment
sets we must know the SPECIFIC Cayley coordinates of both original
interface points, not merely that some representatives exist in
the common source-block image.

The pointwise source-chart certificates of the SAME covered named
history make those coordinates canonical up to proof-irrelevant
casts between equal source-mask indices. Global linkedness of
the original history and the positional active-boundary selection
identify the shared middle Cayley chart literally.

This gives the exact noncommutative displacement equation on
specified original K_A coordinates at every pair of consecutive
selected active boundaries. The remaining proof obligations are
to identify the original actual atom attachment shifts and prove
their normalized triple separation, then assemble the full
proper-M chain quotient and completed letter actions.
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

/-- The REAL historical boundary occurrences P,Q have exactly
the correct original Cayley coordinates for their actual chosen
attaching parameters. Their unique normalized K_(M∩A) shift
satisfies the equation with these SPECIFIC endpoints.

The only global premises are linkedness and pointwise correctness,
both already proved for the canonical original covered history. -/
theorem CoveredNamedAlignedHistory.internal_pair_exact_shift
    {M : Proper S}
    (H : CoveredNamedAlignedHistory D S old L M)
    (hlinked : AlignedBoundaryList.Linked D S old L H.aligned)
    (hpoint : H.AllPointwise D S old L)
    (q : H.named.data.chain.state.Space)
    (front active :
      List (NamedHistoricalBlock D S old L M H.named.data.chain))
    (P Q : AlignedNamedBoundary D S old L M H.named.data.chain)
    (pref suffix : List
      (AlignedNamedBoundary D S old L M H.named.data.chain))
    (hpair :
      (H.aligned.drop front.length).take (active.length - 1) =
        pref ++ P :: Q :: suffix)
    (cP : P.InterfaceChoice D S old L q)
    (cQ : Q.InterfaceChoice D S old L q) :
    let hMiddle : P.rightNamed = Q.leftNamed :=
      alignedBoundaryList_adjacent_middle_eq
        D S old L
        ((H.aligned.drop front.length).take (active.length - 1))
        (H.internal_boundaries_linked D S old L
          hlinked front active)
        pref P Q suffix hpair
    let x := P.rightNamedCoordinate D S old L cP.parameter
    let y := sourceMaskCast S old
      (congrArg
        (fun T : NamedHistoricalBlock D S old L M
          H.named.data.chain => T.source) hMiddle).symm
      (Q.leftNamedCoordinate D S old L cQ.parameter)
    ∃! shift : (old (Step.meet S M P.rightNamed.source)).Carrier,
      x * (L (Step.meet S M P.rightNamed.source)
        P.rightNamed.source Finset.inter_subset_right).incl shift = y := by
  let hMiddle : P.rightNamed = Q.leftNamed :=
    alignedBoundaryList_adjacent_middle_eq
      D S old L
      ((H.aligned.drop front.length).take (active.length - 1))
      (H.internal_boundaries_linked D S old L hlinked front active)
      pref P Q suffix hpair
  have hpSel : P ∈ (H.aligned.drop front.length).take
      (active.length - 1) := by
    rw [hpair]
    simp
  have hqSel : Q ∈ (H.aligned.drop front.length).take
      (active.length - 1) := by
    rw [hpair]
    simp
  have hpHist : P ∈ H.aligned :=
    List.mem_of_mem_drop (List.mem_of_mem_take hpSel)
  have hqHist : Q ∈ H.aligned :=
    List.mem_of_mem_drop (List.mem_of_mem_take hqSel)
  exact P.adjacent_exact_coordinate_shift D S old L
    Q hMiddle (hpoint P hpHist) (hpoint Q hqHist)
    q cP.parameter cQ.parameter cP.reached cQ.reached

/-- On the genuine finite original separated LinkChain, both
linkedness and pointwise Cayley coordinate correctness are
automatically discharged by their independent checked inductions
on the SAME covered named historical record. -/
theorem coveredBuildNonempty_internal_pair_exact_shift
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms)
    (q : (coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep).named.data.chain.state.Space)
    (front active :
      List (NamedHistoricalBlock D S old L M
        (coveredNamedAlignedBuildNonempty D S old L M
          atoms hatoms hsep).named.data.chain))
    (P Q : AlignedNamedBoundary D S old L M
      (coveredNamedAlignedBuildNonempty D S old L M
        atoms hatoms hsep).named.data.chain)
    (pref suffix : List
      (AlignedNamedBoundary D S old L M
        (coveredNamedAlignedBuildNonempty D S old L M
          atoms hatoms hsep).named.data.chain))
    (hpair :
      ((coveredNamedAlignedBuildNonempty D S old L M
        atoms hatoms hsep).aligned.drop front.length).take
          (active.length - 1) = pref ++ P :: Q :: suffix)
    (cP : P.InterfaceChoice D S old L q)
    (cQ : Q.InterfaceChoice D S old L q) :
    let H := coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep
    let hMiddle : P.rightNamed = Q.leftNamed :=
      alignedBoundaryList_adjacent_middle_eq D S old L
        ((H.aligned.drop front.length).take (active.length - 1))
        (H.internal_boundaries_linked D S old L
          (coveredNamedAlignedBuildNonempty_linked
            D S old L M atoms hatoms hsep)
          front active)
        pref P Q suffix hpair
    let x := P.rightNamedCoordinate D S old L cP.parameter
    let y := sourceMaskCast S old
      (congrArg
        (fun T : NamedHistoricalBlock D S old L M
          H.named.data.chain => T.source) hMiddle).symm
      (Q.leftNamedCoordinate D S old L cQ.parameter)
    ∃! shift : (old (Step.meet S M P.rightNamed.source)).Carrier,
      x * (L (Step.meet S M P.rightNamed.source)
        P.rightNamed.source Finset.inter_subset_right).incl shift = y := by
  let H := coveredNamedAlignedBuildNonempty D S old L M
    atoms hatoms hsep
  exact H.internal_pair_exact_shift D S old L
    (coveredNamedAlignedBuildNonempty_linked D S old L
      M atoms hatoms hsep)
    (coveredNamedAlignedBuildNonempty_allPointwise D S old L
      M atoms hatoms hsep)
    q front active P Q pref suffix hpair cP cQ

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
