import GluingEPPA.Steiner.ChainValuation.NamedBoundaryMaskAlignment

/-!
# The named Cayley history and witnessed boundary history share one chain

There are two useful refinements of the literal separated LinkChain:
a source-named family of historical coset charts, and a list of exact
historical attachment interfaces. Their component and interface
theorems are not sufficient for a global normalization unless they
refer to the SAME actual pushout state.

This file couples them from their common one-block base and maintains
the equality of the *actual BuildResult records* through every
separated LinkChain.step. In particular, the last group and quotient
state are not merely equivalent: the two fields refer to the same
recursive state after forgetting their respective proof data.

Finite-list recursion and the global normalized M-component chart
remain separate theorems.
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

/-- Both certified histories are refinements of exactly the same
original, dependent LinkChain.BuildResult. -/
structure CoupledNamedBoundaryHistory (M : Proper S) where
  named : NamedHistoryBuildResult D S old L M
  boundary : BoundaryHistoryBuildResult D S old L M
  sameChain : named.data.chain = boundary.chain

/-- The singleton original Link chain has one historical Cayley block
and no historical attachment boundary; the two records agree literally. -/
noncomputable def coupledHistoryInitial (M : Proper S) (x : Atom S old) :
    CoupledNamedBoundaryHistory D S old L M where
  named := namedHistoryInitial D S old L M x
  boundary := boundaryHistoryInitial D S old L M x
  sameChain := rfl

/-- Every genuine LinkChain attachment transports both histories
together. The dependent proof that permits the attachment is
transported through the equality of their *original* chains.
No new pushout state is constructed. -/
noncomputable def coupledHistoryStep
    (M : Proper S) (H : CoupledNamedBoundaryHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.named.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.named.data.chain.current y) :
    CoupledNamedBoundaryHistory D S old L M := by
  have hBoundarySep :
      (match H.boundary.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.boundary.chain.current y) := by
    rw [← H.sameChain]
    exact hsep
  let N := namedHistoryStep D S old L M H.named y hsep
  let B := boundaryHistoryStep D S old L M H.boundary y hBoundarySep
  refine
    { named := N
      boundary := B
      sameChain := ?_ }
  change
    step D S old L H.named.data.chain y hsep =
      step D S old L H.boundary.chain y hBoundarySep
  rw [H.sameChain]

/-- The coupled state inherits quotient coverage from the genuine
source-named history, without needing to recompute an abstract
component history or postulate a common full-stage group. -/
theorem CoupledNamedBoundaryHistory.covered
    (M : Proper S) (H : CoupledNamedBoundaryHistory D S old L M) :
    GluingEPPA.Steiner.ChainValuation.HistoricalBlocksCover
      (block S old H.named.data.chain.current.1)
      H.named.data.chain.state M.val
      (H.named.named.map (fun T => T.toHistorical D S old L)) :=
  H.named.covers D S old L M

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
