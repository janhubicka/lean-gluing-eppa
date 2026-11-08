import GluingEPPA.Steiner.ChainValuation.LinkHistoryCorrespondence
import GluingEPPA.Steiner.ChainValuation.LinkHistoryIntervalList

/-!
# Consecutive histories refine the manuscript's literal finite chain

The interval-enriched history of PR #134 has the same underlying
HistorySomeState as the earlier historical-chart builder. PR #108
already established that forgetting that historical-chart builder
recovers exactly LinkChain.buildNonempty.

We retain equality of the *whole* underlying history record (not
only the last Cayley block). In particular, the consecutive-support
certificate belongs to precisely the same quotient space as the
manuscript's original separated-chain realization.

This is not an isomorphism between an M-component and a newly
normalized smaller-mask chain; that final component chart remains
to be built.
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

/-- Adding interval certificates does not change the genuine
historical two-block state or any of its coset charts. -/
theorem intervalHistoryPair_data_eq
    (M : Proper S) (p c : Atom S old) :
    (intervalHistoryPair D S old L M p c).data =
      historyPair D S old L M p c := rfl

/-- Adding interval certificates at the next block does not
alter the underlying historical transition. -/
theorem intervalHistoryNext_data_eq
    (M : Proper S) {p c : Atom S old}
    (H : IntervalHistoryPairResult D S old L M p c)
    (z : Atom S old)
    (hsep : tripleSeparated D S old L p c z) :
    (intervalHistoryNext D S old L M H z hsep).data =
      historyNext D S old L M H.data z hsep := rfl

/-- Every interval-enriched tail forgets to exactly the
earlier historical-tail result, not an auxiliary isomorphic chain. -/
theorem intervalHistoryBuildTail_data_eq
    (M : Proper S) (p c : Atom S old)
    (H : IntervalHistoryPairResult D S old L M p c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (intervalHistoryBuildTail D S old L M p c H rest hsep).data =
      historyBuildTail D S old L M p c H.data rest hsep := by
  induction rest generalizing p c with
  | nil =>
      rfl
  | cons z zs ih =>
      have htriple : tripleSeparated D S old L p c z := hsep.1
      have htail : separatedList D S old L (c :: z :: zs) := hsep.2
      change
        (intervalHistoryBuildTail D S old L M c z
          (intervalHistoryNext D S old L M H z htriple)
          zs htail).data =
        historyBuildTail D S old L M c z
          (historyNext D S old L M H.data z htriple)
          zs htail
      exact ih c z (intervalHistoryNext D S old L M H z htriple) htail

/-- The whole finite interval history, including coverage and
all historical block charts, refines the same history as PR #104. -/
theorem intervalHistoryBuildNonempty_data_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (intervalHistoryBuildNonempty D S old L M atoms hne hsep).data =
      historyBuildNonempty D S old L M atoms hne hsep := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          rfl
      | cons y ys =>
          change
            (intervalHistoryBuildTail D S old L M x y
              (intervalHistoryPair D S old L M x y)
              ys hsep).data =
            historyBuildTail D S old L M x y
              (historyPair D S old L M x y)
              ys hsep
          exact intervalHistoryBuildTail_data_eq D S old L M
            x y (intervalHistoryPair D S old L M x y) ys hsep

/-- The certified interval model is literally the manuscript's
original finite-chain realization after forgetting chart data. -/
theorem intervalHistoryBuildNonempty_result_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (intervalHistoryBuildNonempty D S old L M atoms hne hsep).data.result =
      buildNonempty D S old L atoms hne hsep := by
  calc
    (intervalHistoryBuildNonempty D S old L M atoms hne hsep).data.result =
      (historyBuildNonempty D S old L M atoms hne hsep).result :=
        congrArg (fun T : HistorySomeState D S old L M => T.result)
          (intervalHistoryBuildNonempty_data_eq D S old L M atoms hne hsep)
    _ = buildNonempty D S old L atoms hne hsep :=
        historyBuildNonempty_result_eq D S old L M atoms hne hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
