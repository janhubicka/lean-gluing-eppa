import GluingEPPA.Steiner.ChainValuation.LinkHistoryIntervalStep
import GluingEPPA.Steiner.ChainValuation.LinkHistoryList

/-!
# Consecutive historical support for every finite separated LinkChain

The verified `historyStep` interval theorem is iterated using the
same pair, next, tail, and nonempty-list recursion as the literal
`LinkChain.buildNonempty` construction. At every stage we retain:
* the genuine earlier Link Cayley-state history;
* the full historical-chart coverage and last-mask coset invariant;
* consecutive historical support of every M-component;
* the actual last-block historical chart.

This module adds no full-stage K_S and no new induction hypothesis.
It is a finite-list component-support theorem, not yet the
normalized smaller-mask chain quotient equivalence.
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

/-- A genuine two-block Link history, augmented with the checked
consecutive-interval and last-block-chart invariants. -/
structure IntervalHistoryPairResult (M : Proper S) (p c : Atom S old) where
  data : HistoryPairResult D S old L M p c
  consecutive : AllComponentsConsecutive
    (block S old c.1) data.result.state M.val data.history
  lastChart : HasLastHistoricalChart
    (block S old c.1) data.result.state M.val data.history

/-- The pair base case follows from the true first history and one
literal `LinkChain.historyStep`. -/
noncomputable def intervalHistoryPair
    (M : Proper S) (p c : Atom S old) :
    IntervalHistoryPairResult D S old L M p c := by
  let H := historyInitial D S old L M p
  let R := historyPair D S old L M p c
  refine { data := R, consecutive := ?_, lastChart := ?_ }
  · exact historyStep_allConsecutive D S old L M H c trivial
      (historyInitial_allConsecutive D S old L M p)
      (historyInitial_hasLast D S old L M p)
  · exact historyStep_hasLast D S old L M H c trivial

/-- The actual `historyNext` preserves both invariants, with the
same triple separation assumption as the manuscript recursor. -/
noncomputable def intervalHistoryNext
    (M : Proper S) {p c : Atom S old}
    (H : IntervalHistoryPairResult D S old L M p c)
    (z : Atom S old) (hsep : tripleSeparated D S old L p c z) :
    IntervalHistoryPairResult D S old L M c z := by
  let BR : BuildResult D S old L :=
    { previous := some p
      current := c
      state := H.data.result.state
      entry_spec := H.data.result.entry_spec }
  let HB : HistoryBuildResult D S old L M :=
    { chain := BR
      lastInv := H.data.lastInv
      history := H.data.history
      covered := H.data.covered }
  let N := historyNext D S old L M H.data z hsep
  have hstep :
      match HB.chain.previous with
      | none => True
      | some p' => tripleSeparated D S old L p' HB.chain.current z := by
    simpa [HB, BR] using hsep
  refine { data := N, consecutive := ?_, lastChart := ?_ }
  · exact historyStep_allConsecutive D S old L M HB z hstep
      H.consecutive H.lastChart
  · exact historyStep_hasLast D S old L M HB z hstep

/-- The exact terminal history with its full interval invariant. -/
structure IntervalHistorySomeState (M : Proper S) where
  data : HistorySomeState D S old L M
  consecutive : AllComponentsConsecutive
    (block S old data.result.current.1)
    data.result.state M.val data.history
  lastChart : HasLastHistoricalChart
    (block S old data.result.current.1)
    data.result.state M.val data.history

/-- Recursion along every remaining consecutive block of a literal
separated chain, preserving all-component consecutive support. -/
noncomputable def intervalHistoryBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : IntervalHistoryPairResult D S old L M p c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    IntervalHistorySomeState D S old L M :=
  match rest with
  | [] =>
      { data :=
          { result := ⟨c, H.data.result.state⟩
            lastInv := H.data.lastInv
            history := H.data.history
            covered := H.data.covered }
        consecutive := H.consecutive
        lastChart := H.lastChart }
  | z :: zs =>
      intervalHistoryBuildTail M c z
        (intervalHistoryNext D S old L M H z hsep.1)
        zs hsep.2

/-- The full finite-list induction. Unlike a conditional one-step
lemma, it constructs the actual historical state and certifies all its
M-components have consecutive support, for every nonempty
separated list of earlier Link chain atoms. -/
noncomputable def intervalHistoryBuildNonempty
    (M : Proper S) (l : List (Atom S old)) (hne : l ≠ [])
    (hsep : separatedList D S old L l) :
    IntervalHistorySomeState D S old L M := by
  cases l with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          let H := historyInitial D S old L M x
          exact
            { data :=
                { result := ⟨x, H.chain.state⟩
                  lastInv := H.lastInv
                  history := H.history
                  covered := H.covered }
              consecutive := historyInitial_allConsecutive D S old L M x
              lastChart := historyInitial_hasLast D S old L M x }
      | cons y ys =>
          exact intervalHistoryBuildTail D S old L M x y
            (intervalHistoryPair D S old L M x y) ys hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
