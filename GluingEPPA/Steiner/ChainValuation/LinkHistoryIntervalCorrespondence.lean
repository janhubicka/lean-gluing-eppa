import GluingEPPA.Steiner.ChainValuation.LinkHistoryIntervalList

/-!
# The interval-enriched history is literally the original finite builder

The interval-enriched recursive history was deliberately defined by
the very same one-/two-/many-block cases as the already checked
`LinkHistoryList.historyBuildNonempty`. Here we establish equality
of the *underlying records*, including their full pushout carrier,
historical chart list, and coverage/coset invariants.

This bridges the new consecutive-support invariant back to the
manuscript's actual finite-chain builder, rather than merely
constructing a separate isomorphic diagram.
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

/-- Forgetting the additional interval proofs from an enriched tail
returns precisely the original historical tail, without changing
its quotient state or historical chart collection. -/
theorem intervalHistoryBuildTail_data_eq
    (M : Proper S) (p c : Atom S old)
    (H : IntervalHistoryPairResult D S old L M p c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (intervalHistoryBuildTail D S old L M p c H rest hsep).data =
      historyBuildTail D S old L M p c H.data rest hsep := by
  cases rest with
  | nil => rfl
  | cons z zs =>
      change
        (intervalHistoryBuildTail D S old L M c z
          (intervalHistoryNext D S old L M H z hsep.1)
          zs hsep.2).data =
        historyBuildTail D S old L M c z
          (historyNext D S old L M H.data z hsep.1)
          zs hsep.2
      exact intervalHistoryBuildTail_data_eq
        D S old L M c z
        (intervalHistoryNext D S old L M H z hsep.1) zs hsep.2
termination_by rest.length

/-- The original manuscript's concrete nonempty separated-list builder
is definitionally recovered from the interval-enriched constructor
after forgetting the added interval certificates. -/
theorem intervalHistoryBuildNonempty_data_eq
    (M : Proper S) (l : List (Atom S old)) (hne : l ≠ [])
    (hsep : separatedList D S old L l) :
    (intervalHistoryBuildNonempty D S old L M l hne hsep).data =
      historyBuildNonempty D S old L M l hne hsep := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          change
            (intervalHistoryBuildTail D S old L M x y
              (intervalHistoryPair D S old L M x y) ys hsep).data =
            historyBuildTail D S old L M x y
              (historyPair D S old L M x y) ys hsep
          exact intervalHistoryBuildTail_data_eq
            D S old L M x y (intervalHistoryPair D S old L M x y) ys hsep

/-- Consecutive historical support holds for *every* M-component
of the exact original nonempty separated-list history. -/
theorem historyBuildNonempty_allConsecutive
    (M : Proper S) (l : List (Atom S old)) (hne : l ≠ [])
    (hsep : separatedList D S old L l) :
    let H := historyBuildNonempty D S old L M l hne hsep
    AllComponentsConsecutive
      (block S old H.result.current.1) H.result.state
      M.val H.history := by
  let H := intervalHistoryBuildNonempty D S old L M l hne hsep
  have heq : H.data = historyBuildNonempty D S old L M l hne hsep :=
    intervalHistoryBuildNonempty_data_eq D S old L M l hne hsep
  rw [← heq]
  exact H.consecutive

/-- The exact original nonempty historical-list builder also retains
the actual last-block chart. -/
theorem historyBuildNonempty_hasLast
    (M : Proper S) (l : List (Atom S old)) (hne : l ≠ [])
    (hsep : separatedList D S old L l) :
    let H := historyBuildNonempty D S old L M l hne hsep
    HasLastHistoricalChart
      (block S old H.result.current.1) H.result.state
      M.val H.history := by
  let H := intervalHistoryBuildNonempty D S old L M l hne hsep
  have heq : H.data = historyBuildNonempty D S old L M l hne hsep :=
    intervalHistoryBuildNonempty_data_eq D S old L M l hne hsep
  rw [← heq]
  exact H.lastChart

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
