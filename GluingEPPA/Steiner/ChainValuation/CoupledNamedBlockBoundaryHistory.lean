import GluingEPPA.Steiner.ChainValuation.AlignedBoundaryBlockStep

/-!
# One exact original chain carrying both historical blocks and boundaries

The proper-mask component normalization needs to know that the
SOURCE-NAMED historical Cayley block list and the list reconstructed
from consecutive original Link interfaces are actually the SAME
ordered sequence of dependent Cayley charts, not merely lists with
equal lengths and source masks.

Rather than postulating a late isomorphism between two independently
built histories, we maintain that equality as an explicit induction
invariant throughout the literal LinkChain.step recursion. The
block list is advanced by the existing namedHistoricalStepList,
the boundary list by genuine aligned-boundary transport and a
fresh original Link boundary, and their equality is exactly the
one-step result from AlignedBoundaryBlockStep.

The resulting finite history is a genuine refinement of the original
LinkChain construction, preserving all source occurrences and every
original group coordinate. The remaining comparison to the separately
covered named history and normalized component test is downstream.
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

/-- One original partially built LinkChain, with its genuine
source-named Cayley charts and the corresponding exact historical
interfaces as ONE single dependent record.

The coherence field identifies the entire named block LIST,
including individual occurrences, with reconstruction from
the original boundary endpoints (not just their masks). -/
structure CoupledNamedBlockBoundaryHistory (M : Proper S) where
  chain : BuildResult D S old L
  lastInv : LastMaskCoset D S old L M chain
  blocks : List (NamedHistoricalBlock D S old L M chain)
  boundaries : List (AlignedNamedBoundary D S old L M chain)
  sameBlocks : blocks =
    alignedBoundaryBlockSequence D S old L
      (namedHistoricalLast D S old L M chain lastInv) boundaries

/-- Base case: one genuine Cayley source block has no boundaries,
and the reconstructed source-block list is its literal last chart. -/
noncomputable def coupledNamedBlockBoundaryInitial
    (M : Proper S) (x : Atom S old) :
    CoupledNamedBlockBoundaryHistory D S old L M where
  chain := initial D S old L x
  lastInv := initial_lastMaskCoset D S old L M x
  blocks := [namedHistoricalLast D S old L M
    (initial D S old L x)
    (initial_lastMaskCoset D S old L M x)]
  boundaries := []
  sameBlocks := rfl

/-- Each actual original separated LinkChain.step transports the
named source blocks, transports all earlier aligned interfaces,
adds the one true new boundary, and preserves their EXACT
block-occurrence correspondence. -/
noncomputable def coupledNamedBlockBoundaryStep
    (M : Proper S)
    (H : CoupledNamedBlockBoundaryHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p H.chain.current y) :
    CoupledNamedBlockBoundaryHistory D S old L M := by
  let R := H.chain
  let hcoset := H.lastInv
  let nextBlocks :=
    namedHistoricalStepList D S old L M R y hsep hcoset H.blocks
  let nextBoundaries :=
    H.boundaries.map (fun P =>
      P.transport D S old L y hsep hcoset) ++
    [alignedNamedBoundaryFresh D S old L M R y hsep hcoset]
  refine
    { chain := step D S old L R y hsep
      lastInv := step_lastMaskCoset D S old L M R y hsep hcoset
      blocks := nextBlocks
      boundaries := nextBoundaries
      sameBlocks := ?_ }
  change
    namedHistoricalStepList D S old L M R y hsep hcoset H.blocks =
      alignedBoundaryBlockSequence D S old L
        (namedHistoricalLast D S old L M
          (step D S old L R y hsep)
          (step_lastMaskCoset D S old L M R y hsep hcoset))
        (H.boundaries.map (fun P =>
          P.transport D S old L y hsep hcoset) ++
          [alignedNamedBoundaryFresh D S old L M R y hsep hcoset])
  rw [H.sameBlocks]
  exact (alignedBoundaryBlockSequence_step
    D S old L M R y hsep hcoset H.boundaries).symm

/-- The exact original finite list tail, preserving one common
source-named block and aligned boundary history through all steps. -/
noncomputable def coupledNamedBlockBoundaryBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : CoupledNamedBlockBoundaryHistory D S old L M)
    (hp : H.chain.previous = some p)
    (hc : H.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    CoupledNamedBlockBoundaryHistory D S old L M := by
  induction rest generalizing p c H with
  | nil => exact H
  | cons z zs ih =>
      have hstep :
          (match H.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous H.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coupledNamedBlockBoundaryStep D S old L M H z hstep
      have hnp : HN.chain.previous = some c := by
        change some H.chain.current = some c
        rw [hc]
      have hnc : HN.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- An arbitrary genuine finite nonempty separated LinkChain,
carrying BOTH original historical source blocks and exact
aligned interfaces with their identity maintained at each step.

This is the same left-to-right step recursion as the manuscript,
and never replaces the quotient or the earlier Cayley groups. -/
noncomputable def coupledNamedBlockBoundaryBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    CoupledNamedBlockBoundaryHistory D S old L M := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact coupledNamedBlockBoundaryInitial D S old L M x
      | cons y ys =>
          let H0 := coupledNamedBlockBoundaryInitial
            D S old L M x
          let H1 := coupledNamedBlockBoundaryStep
            D S old L M H0 y trivial
          have hp : H1.chain.previous = some x := rfl
          have hc : H1.chain.current = y := rfl
          exact coupledNamedBlockBoundaryBuildTail
            D S old L M x y H1 hp hc ys hsep

/-- The full finite genuine historical Cayley block occurrence
list is EXACTLY the list reconstructed from the consecutive
original aligned Link boundaries, not just bijective to it. -/
theorem coupledNamedBlockBoundaryBuildNonempty_sameBlocks
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coupledNamedBlockBoundaryBuildNonempty
      D S old L M atoms hne hsep
    H.blocks = alignedBoundaryBlockSequence D S old L
      (namedHistoricalLast D S old L M
        H.chain H.lastInv) H.boundaries := by
  intro H
  exact H.sameBlocks

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
