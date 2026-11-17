import GluingEPPA.Steiner.ChainValuation.LinkedAlignedBoundaryFinite

/-!
# Extract the common historical Cayley chart at two consecutive positions

The checked finite linked-history invariant asserts the correct
middle chart for every consecutive pair of boundaries. To use it
when normalizing a *selected active interval*, we need an ordinary
statement with a pair of boundary occurrences, not a recursive
list predicate.

If the original boundary history decomposes as pref followed
by P,Q and suffix, linkedness yields literal equality of the
named right chart of P and named left chart of Q. The proof makes
no assumption that source masks or boundaries are distinct and
is therefore valid even when the same mask occurs repeatedly.

This is precisely the hMiddle premise required by the unique
K_(M intersection A) interior displacement lemma.
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

/-- Any two actual consecutive boundary occurrences in a
linked history share exactly the same dependent named Cayley
middle-block chart, not merely an isomorphic carrier or mask. -/
theorem alignedBoundaryList_adjacent_middle_eq
    {M : Proper S} {R : BuildResult D S old L}
    (history : List (AlignedNamedBoundary D S old L M R))
    (hlinked : AlignedBoundaryList.Linked D S old L history)
    (pref : List (AlignedNamedBoundary D S old L M R))
    (P Q : AlignedNamedBoundary D S old L M R)
    (suffix : List (AlignedNamedBoundary D S old L M R))
    (heq : history = pref ++ P :: Q :: suffix) :
    P.rightNamed = Q.leftNamed := by
  have aux : ∀ pre : List (AlignedNamedBoundary D S old L M R),
      AlignedBoundaryList.Linked D S old L
        (pre ++ P :: Q :: suffix) →
        P.rightNamed = Q.leftNamed := by
    intro pre
    induction pre with
    | nil =>
        intro h
        exact h.1
    | cons a rest ih =>
        intro h
        cases rest with
        | nil =>
            change a.rightNamed = P.leftNamed ∧
              AlignedBoundaryList.Linked D S old L (P :: Q :: suffix) at h
            exact ih h.2
        | cons b tail =>
            change a.rightNamed = b.leftNamed ∧
              AlignedBoundaryList.Linked D S old L
                (b :: tail ++ P :: Q :: suffix) at h
            exact ih h.2
  rw [heq] at hlinked
  exact aux pref hlinked

/-- In the original finite separated LinkChain construction,
each consecutive pair of the aligned true historical boundary
records is connected by the identical named middle block.

This gives the literal coordinate equality used as hMiddle in
the normalized interior-shift theorem, for every actual position.
-/
theorem buildNonempty_adjacent_middle_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := linkedAlignedBuildNonempty D S old L M atoms hne hsep
    ∀ (P Q : AlignedNamedBoundary D S old L M
        H.data.boundaryHistory.chain)
      (pref suffix : List (AlignedNamedBoundary D S old L M
        H.data.boundaryHistory.chain)),
      H.data.aligned = pref ++ P :: Q :: suffix →
      P.rightNamed = Q.leftNamed := by
  intro H P Q pref suffix heq
  exact alignedBoundaryList_adjacent_middle_eq D S old L
    H.data.aligned H.linked pref P Q suffix heq

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
