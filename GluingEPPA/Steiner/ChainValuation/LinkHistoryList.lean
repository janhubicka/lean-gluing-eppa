import GluingEPPA.Steiner.ChainValuation.LinkHistoryStep
import GluingEPPA.Steiner.ChainValuation.LinkChainListCoset

/-!
# Historical component charts for every complete separated LinkChain list

This file extends the actual checked one-step history constructor along
the same one-/two-/many-block pattern used by LinkChain.buildNonempty.
No common ambient larger group is introduced: every historical block
retains its own earlier Cayley group and exact restricted subgroup.

The resulting list is a history for a concrete chain with complete
coverage of all actual quotient vertices, and the same last-block
coset invariant. The next step is the normalized smaller-alphabet
component chart and its genuine-edge reflection.
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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- The genuine pair-stage quotient and its entire historical chart
collection, for two consecutively attached earlier Cayley blocks. -/
structure HistoryPairResult (M : Proper S) (p c : Atom S old) where
  result : PairResult D S old L p c
  lastInv :
    LastBlockCosetInvariant (block S old c.1) result.state M.val
      (restrictedSubgroup D S old L M c.1)
  history : List (HistoricalBlock (block S old c.1) result.state M.val)
  covered : HistoricalBlocksCover
    (block S old c.1) result.state M.val history

/-- Two-block base case, preserving precisely the actual pair state. -/
noncomputable def historyPair (M : Proper S) (p c : Atom S old) :
    HistoryPairResult D S old L M p c := by
  let H := historyStep D S old L M
    (historyInitial D S old L M p) c trivial
  exact
    { result := pair D S old L p c
      lastInv := H.lastInv
      history := H.history
      covered := H.covered }

/-- The next literal pair of blocks retains all older charts and
appends exactly the new last Cayley block. -/
noncomputable def historyNext
    (M : Proper S) {p c : Atom S old}
    (H : HistoryPairResult D S old L M p c)
    (z : Atom S old)
    (hsep : tripleSeparated D S old L p c z) :
    HistoryPairResult D S old L M c z := by
  let BR : BuildResult D S old L :=
    { previous := some p
      current := c
      state := H.result.state
      entry_spec := H.result.entry_spec }
  let HB : HistoryBuildResult D S old L M :=
    { chain := BR
      lastInv := H.lastInv
      history := H.history
      covered := H.covered }
  let HN := historyStep D S old L M HB z (by simpa using hsep)
  exact
    { result := next D S old L H.result z hsep
      lastInv := HN.lastInv
      history := HN.history
      covered := HN.covered }

/-- A terminal chain package with all its historical block cosets.
Its carrier and current atom are those of the real SomeState API. -/
structure HistorySomeState (M : Proper S) where
  result : SomeState S old
  lastInv :
    LastBlockCosetInvariant (block S old result.current.1)
      result.state M.val
      (restrictedSubgroup D S old L M result.current.1)
  history : List
    (HistoricalBlock (block S old result.current.1) result.state M.val)
  covered : HistoricalBlocksCover
    (block S old result.current.1) result.state M.val history

/-- Iterate the same recursion on the list of extra blocks as in
LinkChain.buildTail, transporting every historical coset chart. -/
noncomputable def historyBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : HistoryPairResult D S old L M p c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    HistorySomeState D S old L M :=
  match rest with
  | [] =>
      { result := ⟨c, H.result.state⟩
        lastInv := H.lastInv
        history := H.history
        covered := H.covered }
  | z :: zs =>
      historyBuildTail D S old L M c z
        (historyNext D S old L M H z hsep.1)
        zs hsep.2

/-- Every nonempty separated list has a literal realized
history of all earlier Cayley blocks, each with an injective
restricted-coset chart and complete quotient coverage. -/
noncomputable def historyBuildNonempty
    (M : Proper S) (l : List (Atom S old)) (hne : l ≠ [])
    (hsep : separatedList D S old L l) :
    HistorySomeState D S old L M := by
  cases l with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          let H := historyInitial D S old L M x
          exact
            { result := ⟨x, H.chain.state⟩
              lastInv := H.lastInv
              history := H.history
              covered := H.covered }
      | cons y ys =>
          exact historyBuildTail D S old L M x y
            (historyPair D S old L M x y) ys hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
