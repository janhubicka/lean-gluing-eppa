import GluingEPPA.Steiner.ChainValuation.HistoricalComponentSlices
import GluingEPPA.Steiner.ChainValuation.LinkStepComponentMatching

/-!
# A complete history of actual LinkChain construction steps

The manuscript's BuildResult.step records the last block, the prior
block and the literal quotient ChainState. We package its *finite list*
of heterogeneous historical Cayley blocks with their injective coset
charts, the last-block invariant and coverage of the entire quotient.
All historical component statements are about genuine M-coloured paths
in the currently constructed chain.

This is the actual one-step and base-case history induction. It does
not yet create the record for an arbitrary full separated list.
It does not identify a proper component with a smaller chain test.
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

/-- The actual finite chain and its complete heterogeneous Cayley
history at a fixed restricted alphabet M. -/
structure HistoryBuildResult (M : Proper S) where
  chain : BuildResult D S old L
  lastInv : LastMaskCoset D S old L M chain
  history : List
    (HistoricalBlock (block S old chain.current.1) chain.state M.val)
  covered : HistoricalBlocksCover
    (block S old chain.current.1) chain.state M.val history

/-- The actual initial one-block chain has a complete, covered
history, consisting of exactly its original group. -/
noncomputable def historyInitial (M : Proper S) (x : Atom S old) :
    HistoryBuildResult D S old L M := by
  let R := initial D S old L x
  let hlast : LastMaskCoset D S old L M R :=
    initial_lastMaskCoset D S old L M x
  let A := block S old x.1
  let P := restrictedSubgroup D S old L M x.1
  exact
    { chain := R
      lastInv := hlast
      history := [historicalBlock_last A R.state M.val P hlast]
      covered := historicalBlocks_first_cover A M.val P hlast }

/-- A manuscript LinkChain.step preserves all old historical
coset charts, appends the new last block, and maintains coverage. -/
noncomputable def historyStep
    (M : Proper S) (H : HistoryBuildResult D S old L M)
    (y : Atom S old)
    (hsep :
      match H.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.chain.current y) :
    HistoryBuildResult D S old L M := by
  let R := H.chain
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi : Function.Injective i :=
    left_injective D S old L R.current.1 y.1
  have hj : Function.Injective j :=
    right_injective D S old L R.current.1 y.1
  have hd : Disjoint R.state.entry
      (exitSet A R.current.2 i) :=
    step_attachment_disjoint D S old L R y hsep
  have hs : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : (old (common S R.current.1 y.1)).Carrier,
        i k = A.edge e ∧ j k = B.edge e := by
    intro e heA heB
    exact shared_edge D S old L R.current.1 y.1 e heA heB
  have hpull : AttachmentReachCompatible A B
      R.state R.current.2 i j M.val :=
    step_attachment_compatible D S old L M R y H.lastInv
  have hlast : LastMaskCoset D S old L M
      (step D S old L R y hsep) :=
    step_lastMaskCoset D S old L M R y hsep H.lastInv
  let Q := restrictedSubgroup D S old L M y.1
  let history' := historicalBlocks_extend
    A B R.state R.current.2 i j hi hj hd hs
    M.val hpull Q hlast H.history
  have hcover : HistoricalBlocksCover B
      (GluingEPPA.Steiner.ChainValuation.extend
        A B R.state R.current.2 i j hi hj hd hs)
      M.val history' :=
    historicalBlocks_extend_cover
      A B R.state R.current.2 i j hi hj hd hs
      M.val hpull Q hlast H.history H.covered
  exact
    { chain := step D S old L R y hsep
      lastInv := hlast
      history := history'
      covered := hcover }

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
