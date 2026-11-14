import GluingEPPA.Steiner.ChainValuation.NamedHistoricalForgetful

/-!
# One-step original historical chart history with named source masks

The existing HistoryBuildResult retains the true quotient, all old
restricted-coset charts and complete coverage, but forgets which
original earlier mask A indexes each chart.

This record adds the actual source masks while proving that forgetting
them returns *exactly* the existing chart list. The initial case and
one genuine separated LinkChain step preserve the invariant; no
surrogate quotient, global group, or unproved source matching is used.

The finite-list recursor and global normalized component chart are
separate tasks.
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

open GluingEPPA.Steiner.ChainValuation

/-- The exact original historical state, decorated by genuine masks.
The underlying heterogeneous chart list remains definitionally the
one used by the established full-chain component-interval induction. -/
structure NamedHistoryBuildResult (M : Proper S) where
  data : HistoryBuildResult D S old L M
  named : List (NamedHistoricalBlock D S old L M data.chain)
  sourceMasks : List (Proper S)
  sources :
    named.map (fun T => T.source) = sourceMasks
  forget :
    named.map (fun T => T.toHistorical D S old L) = data.history

/-- The original singleton Cayley chain has exactly one named source
group, and forgetting that name recovers the covered generic chart. -/
noncomputable def namedHistoryInitial (M : Proper S) (x : Atom S old) :
    NamedHistoryBuildResult D S old L M := by
  let H := historyInitial D S old L M x
  refine
    { data := H
      named := [namedHistoricalLast D S old L M H.chain H.lastInv]
      sourceMasks := [x.1]
      sources := ?_
      forget := ?_ }
  · rfl
  · rfl

/-- One actual LinkChain.step transports every original source mask
unchanged, appends the new last mask, and produces the *same*
heterogeneous historical block list after forgetting the names. -/
noncomputable def namedHistoryStep
    (M : Proper S) (H : NamedHistoryBuildResult D S old L M)
    (y : Atom S old)
    (hsep :
      match H.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.data.chain.current y) :
    NamedHistoryBuildResult D S old L M := by
  let H' := historyStep D S old L M H.data y hsep
  let named' := namedHistoricalStepList D S old L M
    H.data.chain y hsep H.data.lastInv H.named
  refine
    { data := H'
      named := named'
      sourceMasks := H.sourceMasks ++ [y.1]
      sources := ?_
      forget := ?_ }
  · calc
      named'.map (fun T => T.source) =
          H.named.map (fun T => T.source) ++ [y.1] :=
        namedHistoricalStep_sourceList D S old L M
          H.data.chain y hsep H.data.lastInv H.named
      _ = H.sourceMasks ++ [y.1] := by rw [H.sources]
  · have hfor := namedHistoricalStepList_forget D S old L M
        H.data.chain y hsep H.data.lastInv H.named
    calc
      named'.map (fun T => T.toHistorical D S old L) =
          historicalBlocks_extend
            (block S old H.data.chain.current.1) (block S old y.1)
            H.data.chain.state H.data.chain.current.2
            (left D S old L H.data.chain.current.1 y.1)
            (right D S old L H.data.chain.current.1 y.1)
            (left_injective D S old L H.data.chain.current.1 y.1)
            (right_injective D S old L H.data.chain.current.1 y.1)
            (step_attachment_disjoint D S old L H.data.chain y hsep)
            (fun e heA heB =>
              shared_edge D S old L H.data.chain.current.1 y.1 e heA heB)
            M.val
            (step_attachment_compatible D S old L M H.data.chain y H.data.lastInv)
            (restrictedSubgroup D S old L M y.1)
            (step_lastMaskCoset D S old L M H.data.chain y hsep H.data.lastInv)
            (H.named.map (fun T => T.toHistorical D S old L)) := hfor
      _ = H'.history := by rw [H.forget]; rfl

/-- The source-masked family covers the genuine current quotient
because its forgetful list is the already proven covered history. -/
theorem NamedHistoryBuildResult.covers
    (M : Proper S) (H : NamedHistoryBuildResult D S old L M) :
    HistoricalBlocksCover
      (block S old H.data.chain.current.1)
      H.data.chain.state M.val
      (H.named.map (fun T => T.toHistorical D S old L)) := by
  rw [H.forget]
  exact H.data.covered

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
