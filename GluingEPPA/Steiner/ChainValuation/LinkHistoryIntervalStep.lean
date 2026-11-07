import GluingEPPA.Steiner.ChainValuation.HistoricalAllRootInterval
import GluingEPPA.Steiner.ChainValuation.LinkHistoryStep

/-!
# Consecutive-component histories for the manuscript LinkChain

The checked generic all-root step applies to the concrete
`HistoryBuildResult` of the recursive earlier Link family. This
module establishes the one-block base case and the actual
`historyStep` induction step, without assuming any full-stage K_S.

The full finite-list statement must additionally follow the
`buildNonempty` list recursor, retaining literal correspondences
between its states and this history.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]

/-- Any one historical block has consecutive support: the
single index is either active or inactive. -/
theorem singletonHistorical_allConsecutive
    (A : GroupBlock E) (C : ChainState E A)
    (M : Finset E) (T : HistoricalBlock A C M) :
    AllComponentsConsecutive A C M [T] := by
  intro q
  let P : Prop := T.Meets A C M q
  change IsConsecutiveSupport [P]
  classical
  by_cases hp : P
  · refine ⟨[], [P], [], rfl, ?_, ?_, ?_⟩
    · intro p h
      simp at h
    · intro p h
      have heq : p = P := List.mem_singleton.mp h
      subst p
      exact hp
    · intro p h
      simp at h
  · refine ⟨[P], [], [], rfl, ?_, ?_, ?_⟩
    · intro p h
      have heq : p = P := List.mem_singleton.mp h
      subst p
      exact hp
    · intro p h
      simp at h
    · intro p h
      simp at h

end GluingEPPA.Steiner.ChainValuation

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

/-- The initial true Link history has consecutively supported
M-components for every possible root. -/
theorem historyInitial_allConsecutive
    (M : Proper S) (x : Atom S old) :
    AllComponentsConsecutive
      (block S old (historyInitial D S old L M x).chain.current.1)
      (historyInitial D S old L M x).chain.state
      M.val (historyInitial D S old L M x).history := by
  let R := initial D S old L x
  let P := restrictedSubgroup D S old L M x.1
  let hlast : LastMaskCoset D S old L M R :=
    initial_lastMaskCoset D S old L M x
  change AllComponentsConsecutive
    (block S old x.1) R.state M.val
    [historicalBlock_last (block S old x.1) R.state M.val P hlast]
  exact singletonHistorical_allConsecutive
    (block S old x.1) R.state M.val _

/-- The same initial history ends in its actual last Cayley chart. -/
theorem historyInitial_hasLast
    (M : Proper S) (x : Atom S old) :
    HasLastHistoricalChart
      (block S old (historyInitial D S old L M x).chain.current.1)
      (historyInitial D S old L M x).chain.state
      M.val (historyInitial D S old L M x).history := by
  let R := initial D S old L x
  let P := restrictedSubgroup D S old L M x.1
  let hlast : LastMaskCoset D S old L M R :=
    initial_lastMaskCoset D S old L M x
  change HasLastHistoricalChart
    (block S old x.1) R.state M.val
    [historicalBlock_last (block S old x.1) R.state M.val P hlast]
  exact singletonLast_hasLastHistoricalChart
    (block S old x.1) R.state M.val P hlast

/-- The exact concrete `historyStep` preserves the all-component
interval invariant, discharging its compatibility assumptions from
the earlier Link group inclusions and the last-block coset invariant. -/
theorem historyStep_allConsecutive
    (M : Proper S) (H : HistoryBuildResult D S old L M)
    (y : Atom S old)
    (hsep :
      match H.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.chain.current y)
    (hinterval : AllComponentsConsecutive
      (block S old H.chain.current.1) H.chain.state M.val H.history)
    (hlast : HasLastHistoricalChart
      (block S old H.chain.current.1) H.chain.state M.val H.history) :
    let H' := historyStep D S old L M H y hsep
    AllComponentsConsecutive (block S old H'.chain.current.1)
      H'.chain.state M.val H'.history := by
  let R := H.chain
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi := left_injective D S old L R.current.1 y.1
  have hj := right_injective D S old L R.current.1 y.1
  have hd := step_attachment_disjoint D S old L R y hsep
  have hs : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : (old (common S R.current.1 y.1)).Carrier,
        i k = A.edge e ∧ j k = B.edge e := by
    intro e ha hb
    exact shared_edge D S old L R.current.1 y.1 e ha hb
  have hpull := step_attachment_compatible D S old L M R y H.lastInv
  have hnew := step_lastMaskCoset D S old L M R y hsep H.lastInv
  change AllComponentsConsecutive B
      (extend A B R.state R.current.2 i j hi hj hd hs) M.val
      (historicalBlocks_extend A B R.state R.current.2 i j
        hi hj hd hs M.val hpull
        (restrictedSubgroup D S old L M y.1)
        hnew H.history)
  exact historicalBlocks_extend_allConsecutive
    A B R.state R.current.2 i j hi hj hd hs M.val hpull
    (restrictedSubgroup D S old L M y.1)
    hnew H.history hinterval hlast

/-- Last-chart identity is preserved at the actual
manuscript `historyStep`, as well. -/
theorem historyStep_hasLast
    (M : Proper S) (H : HistoryBuildResult D S old L M)
    (y : Atom S old)
    (hsep :
      match H.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.chain.current y) :
    let H' := historyStep D S old L M H y hsep
    HasLastHistoricalChart (block S old H'.chain.current.1)
      H'.chain.state M.val H'.history := by
  let R := H.chain
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi := left_injective D S old L R.current.1 y.1
  have hj := right_injective D S old L R.current.1 y.1
  have hd := step_attachment_disjoint D S old L R y hsep
  have hs : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : (old (common S R.current.1 y.1)).Carrier,
        i k = A.edge e ∧ j k = B.edge e := by
    intro e ha hb
    exact shared_edge D S old L R.current.1 y.1 e ha hb
  have hpull := step_attachment_compatible D S old L M R y H.lastInv
  have hnew := step_lastMaskCoset D S old L M R y hsep H.lastInv
  change HasLastHistoricalChart B
      (extend A B R.state R.current.2 i j hi hj hd hs) M.val
      (historicalBlocks_extend A B R.state R.current.2 i j
        hi hj hd hs M.val hpull
        (restrictedSubgroup D S old L M y.1)
        hnew H.history)
  exact historicalBlocks_extend_hasLast
    A B R.state R.current.2 i j hi hj hd hs M.val hpull
    (restrictedSubgroup D S old L M y.1)
    hnew H.history

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
