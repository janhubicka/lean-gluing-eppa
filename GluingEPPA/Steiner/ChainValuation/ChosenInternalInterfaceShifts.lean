import GluingEPPA.Steiner.ChainValuation.ActiveInternalInterfaceChoices
import GluingEPPA.Steiner.ChainValuation.LinkedAlignedBoundaryPairs
import GluingEPPA.Steiner.ChainValuation.AlignedInteriorShift

/-!
# Genuine consecutive boundary shifts inside the active M-component interval

The previous module chooses a real original K_(A∩B) parameter
at EVERY internal boundary of the actual active historical
M-component interval, keeping repeated masks and boundary
occurrences in order.

To compare two consecutive chosen parameters, it is essential
that their historical boundary records have the SAME dependent
named middle Cayley chart, not merely equal source alphabets.
The globally checked linkedness invariant is inherited by
contiguous slices of the original boundary list. Thus the
already verified unique-displacement theorem applies at
every interior position of the selected component interval.

No uniform ambient group, unrelated diagram isomorphism or
ad hoc chosen separator is introduced. The next step must
identify these interior shifts with the actual normalized
old-link entry/exit parameters and check triple separation.
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

/-- Removing a prefix of actual historical boundary occurrences
does not destroy the literal middle Cayley-chart agreement
between any two remaining consecutive boundary records. -/
theorem alignedBoundaryLinked_drop
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (AlignedNamedBoundary D S old L M R))
    (hlinked : AlignedBoundaryList.Linked D S old L hist)
    (n : Nat) :
    AlignedBoundaryList.Linked D S old L (hist.drop n) := by
  induction n generalizing hist with
  | zero =>
      simpa using hlinked
  | succ n ih =>
      cases hist with
      | nil =>
          trivial
      | cons P rest =>
          change AlignedBoundaryList.Linked D S old L (rest.drop n)
          have hrest :
              AlignedBoundaryList.Linked D S old L rest := by
            cases rest with
            | nil => trivial
            | cons Q tail => exact hlinked.2
          exact ih rest hrest

/-- Keeping an initial segment of a linked historical boundary
list preserves every genuine middle-block chart equality. -/
theorem alignedBoundaryLinked_take
    {M : Proper S} {R : BuildResult D S old L}
    (hist : List (AlignedNamedBoundary D S old L M R))
    (hlinked : AlignedBoundaryList.Linked D S old L hist)
    (n : Nat) :
    AlignedBoundaryList.Linked D S old L (hist.take n) := by
  induction n generalizing hist with
  | zero =>
      trivial
  | succ n ih =>
      cases hist with
      | nil => trivial
      | cons P rest =>
          cases n with
          | zero => trivial
          | succ m =>
              cases rest with
              | nil => trivial
              | cons Q tail =>
                  change P.rightNamed = Q.leftNamed ∧
                    AlignedBoundaryList.Linked D S old L
                      ((Q :: tail).take (m + 1))
                  exact ⟨hlinked.1, ih (Q :: tail) hlinked.2⟩

/-- The exact internal-boundary slice of an active component
interval is linked, with no extra hypothesis on its endpoints
or on distinctness of the original historical source masks. -/
theorem CoveredNamedAlignedHistory.internal_boundaries_linked
    {M : Proper S}
    (H : CoveredNamedAlignedHistory D S old L M)
    (hlinked : AlignedBoundaryList.Linked D S old L H.aligned)
    (front active :
      List (NamedHistoricalBlock D S old L M H.named.data.chain)) :
    AlignedBoundaryList.Linked D S old L
      ((H.aligned.drop front.length).take (active.length - 1)) := by
  exact alignedBoundaryLinked_take D S old L
    (H.aligned.drop front.length)
    (alignedBoundaryLinked_drop D S old L H.aligned
      hlinked front.length)
    (active.length - 1)

/-- Given TWO CONSECUTIVE genuine internal interface parameters
in one actual M-component, their exact middle Cayley coordinates
differ by a UNIQUE element of the true K_(M∩A).

The central named chart equality is derived from original linked
history, not supplied as an assumption or external isomorphism. -/
theorem CoveredNamedAlignedHistory.internal_pair_unique_shift
    {M : Proper S}
    (H : CoveredNamedAlignedHistory D S old L M)
    (hlinked : AlignedBoundaryList.Linked D S old L H.aligned)
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
    ∃ x y : (old P.rightNamed.source).Carrier,
      P.rightNamed.chart.embed x =
        P.boundary.interfaceMap D S old L cP.parameter ∧
      P.rightNamed.chart.embed y =
        Q.boundary.interfaceMap D S old L cQ.parameter ∧
      ∃! shift : (old (Step.meet S M P.rightNamed.source)).Carrier,
        x * (L (Step.meet S M P.rightNamed.source)
          P.rightNamed.source Finset.inter_subset_right).incl shift = y := by
  have hMiddle : P.rightNamed = Q.leftNamed :=
    alignedBoundaryList_adjacent_middle_eq
      D S old L
      ((H.aligned.drop front.length).take (active.length - 1))
      (H.internal_boundaries_linked D S old L hlinked front active)
      pref P Q suffix hpair
  exact P.adjacent_unique_interior_shift D S old L
    Q hMiddle q cP.parameter cQ.parameter cP.reached cQ.reached

/-- On any genuine original covered finite LinkChain history,
linkedness is established by the actual earlier finite recursion.
Thus the interior normalized shift theorem is available for
EVERY consecutive selected pair of real interface parameters. -/
theorem coveredBuildNonempty_internal_pair_unique_shift
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms)
    (q : (coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep).named.data.chain.state.Space)
    (front active : List (NamedHistoricalBlock D S old L M
      (coveredNamedAlignedBuildNonempty D S old L M
        atoms hatoms hsep).named.data.chain))
    (P Q : AlignedNamedBoundary D S old L M
      (coveredNamedAlignedBuildNonempty D S old L M
        atoms hatoms hsep).named.data.chain)
    (pref suffix : List (AlignedNamedBoundary D S old L M
      (coveredNamedAlignedBuildNonempty D S old L M
        atoms hatoms hsep).named.data.chain))
    (hpair :
      ((coveredNamedAlignedBuildNonempty D S old L M
        atoms hatoms hsep).aligned.drop front.length).take
        (active.length - 1) = pref ++ P :: Q :: suffix)
    (cP : P.InterfaceChoice D S old L q)
    (cQ : Q.InterfaceChoice D S old L q) :
    ∃ x y : (old P.rightNamed.source).Carrier,
      P.rightNamed.chart.embed x =
        P.boundary.interfaceMap D S old L cP.parameter ∧
      P.rightNamed.chart.embed y =
        Q.boundary.interfaceMap D S old L cQ.parameter ∧
      ∃! shift : (old (Step.meet S M P.rightNamed.source)).Carrier,
        x * (L (Step.meet S M P.rightNamed.source)
          P.rightNamed.source Finset.inter_subset_right).incl shift = y := by
  let H := coveredNamedAlignedBuildNonempty D S old L M
    atoms hatoms hsep
  exact H.internal_pair_unique_shift D S old L
    (coveredNamedAlignedBuildNonempty_linked D S old L
      M atoms hatoms hsep)
    q front active P Q pref suffix hpair cP cQ

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
