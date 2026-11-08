import GluingEPPA.Steiner.ChainValuation.LinkHistoryCorrespondence
import GluingEPPA.Steiner.ChainValuation.LinkHistoryIntervalCorrespondence

/-!
# The exact manuscript chain carries the interval-support certificate

The interval history and the earlier complete historical chart
construction already agree as whole records. The latter is proved
to agree with the original LinkChain.buildNonempty state (PR #108).

This module records that the finite separated chain used in the
manuscript itself has a complete covering history whose every
M-component occupies a consecutive block interval. Neither a
surrogate quotient nor a top-stage K_S is introduced.

The component's normalization to a smaller-mask separated chain,
including edge reflection, remains a separate theorem.
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

/-- Forgetting the interval certificates produces *exactly* the
original finite LinkChain.buildNonempty realization. -/
theorem intervalHistoryBuildNonempty_result_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (intervalHistoryBuildNonempty D S old L M atoms hne hsep).data.result =
      buildNonempty D S old L atoms hne hsep := by
  calc
    (intervalHistoryBuildNonempty D S old L M atoms hne hsep).data.result =
      (historyBuildNonempty D S old L M atoms hne hsep).result :=
        congrArg
          (fun H : HistorySomeState D S old L M => H.result)
          (intervalHistoryBuildNonempty_data_eq D S old L M atoms hne hsep)
    _ = buildNonempty D S old L atoms hne hsep :=
      historyBuildNonempty_result_eq D S old L M atoms hne hsep

/-- Every M-component of the *original*, literal, finite separated
chain has consecutively supported historical Cayley blocks; those
blocks cover the actual quotient and include its last-block chart.

In particular, this is no longer just a property of an auxiliary
history-building recursor. -/
theorem buildNonempty_has_consecutive_history
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let R := buildNonempty D S old L atoms hne hsep
    ∃ history : List
        (GluingEPPA.Steiner.ChainValuation.HistoricalBlock.{u,u}
          (block S old R.current.1) R.state M.val),
      GluingEPPA.Steiner.ChainValuation.HistoricalBlocksCover
        (block S old R.current.1) R.state M.val history ∧
      GluingEPPA.Steiner.ChainValuation.AllComponentsConsecutive
        (block S old R.current.1) R.state M.val history ∧
      GluingEPPA.Steiner.ChainValuation.HasLastHistoricalChart
        (block S old R.current.1) R.state M.val history := by
  let H := historyBuildNonempty D S old L M atoms hne hsep
  have hEq : H.result = buildNonempty D S old L atoms hne hsep :=
    historyBuildNonempty_result_eq D S old L M atoms hne hsep
  rw [← hEq]
  exact ⟨H.history, H.covered,
    historyBuildNonempty_allConsecutive D S old L M atoms hne hsep,
    historyBuildNonempty_hasLast D S old L M atoms hne hsep⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
