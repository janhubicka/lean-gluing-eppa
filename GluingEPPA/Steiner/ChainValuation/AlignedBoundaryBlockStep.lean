import GluingEPPA.Steiner.ChainValuation.AlignedBoundaryBlockSequence

/-!
# A genuine LinkChain.step preserves the positional named block sequence

To compare the original source-NAMED historical chart list with
the block list reconstructed from the exact historical boundary
records, it is not enough to know only that both lists have the
same masks and length. Their actual dependent Cayley charts
must be IDENTICAL at each position.

This module proves the critical one-step identity. A genuine
LinkChain.step transports every old aligned boundary and appends
the actual new one. Reconstructing source blocks from these
boundary records produces exactly what the original named-block
constructor does: transport all previous genuine named charts
and append the new last named chart.

The singleton base case is included: an empty boundary list
still represents the original single named Cayley block.

Iterating this equality with the original coupled-history
correspondence is the remaining finite-recursion task.
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

/-- Converting a genuine old aligned boundary list to its
source-named historical Cayley-block list commutes with one
literal LinkChain attachment.

Both sides retain the actual K_A source group, original
historical chart embedding, and order of occurrences. -/
theorem alignedBoundaryBlockSequence_step
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (boundaries : List (AlignedNamedBoundary D S old L M R)) :
    let fresh := alignedNamedBoundaryFresh
      D S old L M R y hsep hcoset
    let lastOld := namedHistoricalLast D S old L M R hcoset
    let lastNew := namedHistoricalLast D S old L M
      (step D S old L R y hsep)
      (step_lastMaskCoset D S old L M R y hsep hcoset)
    alignedBoundaryBlockSequence D S old L lastNew
      (boundaries.map (fun P =>
        P.transport D S old L y hsep hcoset) ++ [fresh]) =
    namedHistoricalStepList D S old L M R y hsep hcoset
      (alignedBoundaryBlockSequence D S old L lastOld boundaries) := by
  cases boundaries with
  | nil =>
      rfl
  | cons P rest =>
      simp only [alignedBoundaryBlockSequence,
        namedHistoricalStepList, List.map_append, List.map_cons,
        List.map_map, List.map_singleton, List.cons_append,
        Function.comp_def]
      rfl

/-- The complete original aligned history step has exactly the
named-block-list transition specified by the earlier Link history
constructor, not an independently chosen point-set permutation. -/
theorem alignedNamedStep_blockSequence
    (M : Proper S) (H : AlignedNamedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.boundaryHistory.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
          H.boundaryHistory.chain.current y) :
    let R := H.boundaryHistory.chain
    let oldLast := namedHistoricalLast D S old L M R
      H.boundaryHistory.lastInv
    let newR := step D S old L R y hsep
    let newLast := namedHistoricalLast D S old L M newR
      (step_lastMaskCoset D S old L M R y hsep
        H.boundaryHistory.lastInv)
    alignedBoundaryBlockSequence D S old L newLast
      (alignedNamedStep D S old L M H y hsep).aligned =
    namedHistoricalStepList D S old L M R y hsep
      H.boundaryHistory.lastInv
      (alignedBoundaryBlockSequence D S old L oldLast H.aligned) := by
  exact alignedBoundaryBlockSequence_step
    D S old L M H.boundaryHistory.chain y hsep
    H.boundaryHistory.lastInv H.aligned

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
