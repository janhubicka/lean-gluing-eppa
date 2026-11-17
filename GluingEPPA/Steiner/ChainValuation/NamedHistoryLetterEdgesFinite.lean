import GluingEPPA.Steiner.ChainValuation.NamedHistoricalLetterEdges
import GluingEPPA.Steiner.ChainValuation.NamedHistoryFinite

/-!
# Actual finite-history preservation of each source block's letter edges

The previous one-step theorem gives genuine old-source letter
transitions after every attachment. We iterate it along precisely
the original separated-list recursor for the recursive valuation,
not an independently chosen sequence of group isomorphisms.

For the resulting complete historical list of actual old Cayley
blocks, every letter in a block's source alphabet still has its
genuine matching edge inside that block in the final original
quotient. This is stronger than historical M-coset connectivity.

The whole global normalized M-component chart remains separate.
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

/-- Every original historical block retains all its actual
source-letter edges after any finite sequence of separated
attachments made by the literal LinkChain step constructor. -/
theorem namedHistoryBuildTail_allGenuineLetterEdges
    (M : Proper S) (p c : Atom S old)
    (H : NamedHistoryBuildResult D S old L M)
    (hp : H.data.chain.previous = some p)
    (hc : H.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    H.AllGenuineLetterEdges D S old L →
    (namedHistoryBuildTail D S old L M p c H hp hc rest hsep).AllGenuineLetterEdges
      D S old L := by
  intro hOld
  induction rest generalizing p c H with
  | nil =>
      exact hOld
  | cons z zs ih =>
      have hstep :
          (match H.data.chain.previous with
           | none => True
           | some previous =>
               tripleSeparated D S old L previous H.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := namedHistoryStep D S old L M H z hstep
      have hnp : HN.data.chain.previous = some c := by
        change some H.data.chain.current = some c
        rw [hc]
      have hnc : HN.data.chain.current = z := rfl
      change
        (namedHistoryBuildTail D S old L M c z
          HN hnp hnc zs hsep.2).AllGenuineLetterEdges D S old L
      exact ih c z HN hnp hnc hsep.2
        (namedHistoryStep_allGenuineLetterEdges D S old L M H z hstep hOld)

/-- Each source-named historical K_A chart in any genuine finite
nonempty separated Link chain carries the original matching edge
for EVERY e in A (not only those selected for M). -/
theorem namedHistoryBuildNonempty_allGenuineLetterEdges
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (namedHistoryBuildNonempty D S old L M atoms hne hsep).AllGenuineLetterEdges
      D S old L := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact namedHistoryInitial_allGenuineLetterEdges
            D S old L M x
      | cons y ys =>
          let H0 := namedHistoryInitial D S old L M x
          let H1 := namedHistoryStep D S old L M H0 y trivial
          have hp : H1.data.chain.previous = some x := rfl
          have hc : H1.data.chain.current = y := rfl
          change
            (namedHistoryBuildTail D S old L M x y H1 hp hc
              ys hsep).AllGenuineLetterEdges D S old L
          exact namedHistoryBuildTail_allGenuineLetterEdges
            D S old L M x y H1 hp hc ys hsep
            (namedHistoryStep_allGenuineLetterEdges
              D S old L M H0 y trivial
              (namedHistoryInitial_allGenuineLetterEdges D S old L M x))

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
