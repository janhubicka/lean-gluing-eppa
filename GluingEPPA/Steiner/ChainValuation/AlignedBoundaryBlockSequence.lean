import GluingEPPA.Steiner.ChainValuation.CombinedHistoricalExactCharts

/-!
# Consecutive named Cayley blocks reconstructed from real Link boundaries

The actual aligned boundary history has one fewer entry than the
historical Cayley block list. Each interface records its true left
and right named source block. When consecutive interfaces are
linked, the right named block of one is literally the left named
block of the next.

We reconstruct the ordered named block sequence directly from the
original aligned boundaries, using the actual last historical
source chart only when there is no boundary. Then the list of
CONSECUTIVE block pairs is EXACTLY the original ordered list of
boundary endpoint pairs.

This proves the positional boundary-to-block correspondence at the
level of named dependent source-block records, including repeated
source masks. It does not yet assert equality with the separately
built source-named historical block list; that equality requires
the coupled finite-history recursor and is a subsequent theorem.
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

/-- Exactly one more named historical block occurrence than
genuine boundaries: first left endpoint, then all right endpoints.
For a singleton chain use its genuine last named chart. -/
def alignedBoundaryBlockSequence
    {M : Proper S} {R : BuildResult D S old L}
    (last : NamedHistoricalBlock D S old L M R) :
    List (AlignedNamedBoundary D S old L M R) →
      List (NamedHistoricalBlock D S old L M R)
  | [] => [last]
  | P :: ps =>
      P.leftNamed :: (P :: ps).map (fun B => B.rightNamed)

/-- The genuine adjacent pairs of an ordered list of historical
named Cayley blocks, preserving occurrences and original order. -/
def namedAdjacentBlockPairs
    {M : Proper S} {R : BuildResult D S old L} :
    List (NamedHistoricalBlock D S old L M R) →
      List (NamedHistoricalBlock D S old L M R ×
        NamedHistoricalBlock D S old L M R)
  | a :: b :: rest =>
      (a, b) :: namedAdjacentBlockPairs (b :: rest)
  | _ => []

/-- A reconstructed finite historical source-block sequence
contains exactly one more block than its genuine boundary list. -/
theorem alignedBoundaryBlockSequence_length
    {M : Proper S} {R : BuildResult D S old L}
    (last : NamedHistoricalBlock D S old L M R)
    (boundaries : List (AlignedNamedBoundary D S old L M R)) :
    (alignedBoundaryBlockSequence D S old L last boundaries).length =
      boundaries.length + 1 := by
  cases boundaries with
  | nil => rfl
  | cons P rest =>
      simp only [alignedBoundaryBlockSequence, List.length_cons,
        List.length_map]
      omega

/-- The crucial positional identity: the true boundary records
are precisely the consecutive named Cayley block pairs in the
reconstructed source-block sequence, not just their mask pairs.

A repeated original source mask may occur at several positions;
it is not identified with an earlier occurrence. -/
theorem alignedBoundaryBlockSequence_pairs
    {M : Proper S} {R : BuildResult D S old L}
    (last : NamedHistoricalBlock D S old L M R)
    (boundaries : List (AlignedNamedBoundary D S old L M R))
    (hlink : AlignedBoundaryList.Linked D S old L boundaries) :
    namedAdjacentBlockPairs D S old L
      (alignedBoundaryBlockSequence D S old L last boundaries) =
    boundaries.map (fun P => (P.leftNamed, P.rightNamed)) := by
  induction boundaries with
  | nil => rfl
  | cons P rest ih =>
      cases rest with
      | nil => rfl
      | cons Q tail =>
          have hMiddle : P.rightNamed = Q.leftNamed := hlink.1
          have hTail : AlignedBoundaryList.Linked D S old L
              (Q :: tail) := hlink.2
          change (P.leftNamed, P.rightNamed) ::
              namedAdjacentBlockPairs D S old L
                (P.rightNamed ::
                  (Q :: tail).map (fun T => T.rightNamed)) =
            (P.leftNamed, P.rightNamed) ::
              (Q :: tail).map (fun T => (T.leftNamed, T.rightNamed))
          rw [hMiddle]
          exact congrArg
            (List.cons (P.leftNamed, Q.leftNamed))
            (ih hTail)

/-- Every original finite separated Link chain, on its exact
point and source-chart data, has an ordered synthetic named-block
sequence whose consecutive pairs equal the genuine named endpoint
pairs of all recorded historical boundaries.

The comparison with the standalone source-named history is the
last pending bookkeeping identity needed to select precisely
the internal boundaries of its nonempty active M-interval. -/
theorem alignedNamedBuildNonempty_boundary_block_pairs
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := alignedNamedBuildNonempty D S old L M atoms hne hsep
    let last := namedHistoricalLast D S old L M
      H.boundaryHistory.chain H.boundaryHistory.lastInv
    namedAdjacentBlockPairs D S old L
        (alignedBoundaryBlockSequence D S old L last H.aligned) =
      H.aligned.map (fun P => (P.leftNamed, P.rightNamed)) := by
  intro H last
  exact alignedBoundaryBlockSequence_pairs
    D S old L last H.aligned
    (alignedNamedBuildNonempty_pointwise_and_linked
      D S old L M atoms hne hsep).1

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
