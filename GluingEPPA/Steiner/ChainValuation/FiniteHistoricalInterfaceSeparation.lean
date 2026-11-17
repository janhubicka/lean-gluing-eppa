import GluingEPPA.Steiner.ChainValuation.HistoricalConsecutiveInterfaceDisjoint

/-!
# All consecutive original finite-chain interface images are disjoint

The manuscript's separated Cayley chain is built by the original
one-, two- and many-block LinkChain recursion. Every new attachment
makes the old last entry and its fresh outgoing interface disjoint
in the *actual* quotient. The previous module proves the matching
single-step induction for ALL consecutive historical boundary maps.

This file now iterates the step over the ENTIRE original finite
separated input chain. The result states directly that for every
two consecutive original historical Link boundary occurrences,
their full genuine K_(A∩B) interface point sets are disjoint
in the final quotient. This covers repeated source alphabets
and arbitrary chain length, retaining the exact covered named
history used by the M-component interval proof.

This geometric disjointness is the original-language source
condition from which normalized entry/exit coset separation can
be derived using pointwise Cayley charts and translated subgroup
squares. No normalized chain test or completed theorem is
silently assumed.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E]
variable [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

/-- Iterate actual adjacent-interface separation through the same
original separated LinkChain finite tail as the manuscript. Both
the adjacent disjointness and last-entry data refer to the SAME
covered source-named historical record. -/
theorem coveredNamedAlignedBuildTail_adjacentInterfacesDisjoint
    (M : Proper S) (p c : Atom S old)
    (H : CoveredNamedAlignedHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    HistoricalBoundaryList.AdjacentInterfacesDisjoint
      D S old L H.aligned →
    H.LastInterfaceIsEntry D S old L →
    HistoricalBoundaryList.AdjacentInterfacesDisjoint D S old L
      (coveredNamedAlignedBuildTail D S old L M
        p c H hp hc rest hsep).aligned := by
  induction rest generalizing p c H with
  | nil =>
      intro hOld _
      exact hOld
  | cons z zs ih =>
      intro hOld hLast
      have hstep :
          (match H.named.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coveredNamedAlignedStep D S old L M H z hstep
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2
        (coveredNamedAlignedStep_adjacentInterfacesDisjoint
          D S old L M H z hstep hOld hLast)
        (coveredNamedAlignedStep_lastInterfaceIsEntry
          D S old L M H z hstep)

/-- The entire ORIGINAL finite separated LinkChain has disjoint
interface point sets at every pair of consecutive recorded
historical boundaries. This is a statement in the actual final
quotient, with no auxiliary pushout, anonymous group, or
group-coordinate choice. -/
theorem coveredNamedAlignedBuildNonempty_adjacentInterfacesDisjoint
    (M : Proper S) (atoms : List (Atom S old))
    (hatoms : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coveredNamedAlignedBuildNonempty D S old L M
      atoms hatoms hsep
    HistoricalBoundaryList.AdjacentInterfacesDisjoint
      D S old L H.aligned := by
  cases atoms with
  | nil =>
      exact False.elim (hatoms rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          trivial
      | cons y ys =>
          let H0 := coveredNamedAlignedInitial D S old L M x
          let H1 := coveredNamedAlignedStep D S old L M H0 y trivial
          have hp : H1.named.data.chain.previous = some x := rfl
          have hc : H1.named.data.chain.current = y := rfl
          exact coveredNamedAlignedBuildTail_adjacentInterfacesDisjoint
            D S old L M x y H1 hp hc ys hsep
            (by trivial)
            (coveredNamedAlignedStep_lastInterfaceIsEntry
              D S old L M H0 y trivial)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
