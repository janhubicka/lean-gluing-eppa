import GluingEPPA.Steiner.ChainValuation.NamedHistoryActiveInterval
import GluingEPPA.Steiner.ChainValuation.AlignedBoundaryBlockStep

/-!
# Exact aligned historical boundaries in the already covered named history

A single finite historical chart construction is preferable to
reconciling two independent dependent quotient records. Start with
the previously verified source-NAMED history, which already has
complete component coverage and consecutive M-support, and carry
the entire actual aligned Link boundary list as an extra field.

The invariant states that the source-named historical Cayley block
list is EXACTLY the list reconstructed from those boundary records,
including the first and last block and all repeated occurrences.
The one-step preservation follows directly from the checked
positional boundary-to-block induction lemma. Thus the final
finite result is already the very SAME source-named history whose
nonempty active interval was proved earlier: no late cast, new
quotient or additional chart isomorphism is necessary.

This is the common-state/positional bridge for selecting precisely
the internal boundaries of the active proper-mask interval.
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

/-- The original SOURCE-NAMED covered history, additionally carrying
all actual historical Link boundaries with the precise equality
between the original named block list and their reconstructed
ordered source charts. -/
structure CoveredNamedAlignedHistory (M : Proper S) where
  named : NamedHistoryBuildResult D S old L M
  aligned : List (AlignedNamedBoundary D S old L M named.data.chain)
  blocksAgree : named.named =
    alignedBoundaryBlockSequence D S old L
      (namedHistoricalLast D S old L M
        named.data.chain named.data.lastInv) aligned

/-- The original single-block named historical chain has no
historical boundaries and the required list identity is rfl. -/
noncomputable def coveredNamedAlignedInitial
    (M : Proper S) (x : Atom S old) :
    CoveredNamedAlignedHistory D S old L M where
  named := namedHistoryInitial D S old L M x
  aligned := []
  blocksAgree := rfl

/-- A literal LinkChain.step preserves the complete covered named
Cayley history and extends the original historical boundary
records without changing any source occurrence or group chart.
The positional block-list identity is maintained exactly. -/
noncomputable def coveredNamedAlignedStep
    (M : Proper S) (H : CoveredNamedAlignedHistory D S old L M)
    (y : Atom S old)
    (hsep :
      match H.named.data.chain.previous with
      | none => True
      | some p => tripleSeparated D S old L p
          H.named.data.chain.current y) :
    CoveredNamedAlignedHistory D S old L M := by
  let R := H.named.data.chain
  let hcoset := H.named.data.lastInv
  let N := namedHistoryStep D S old L M H.named y hsep
  let boundaries := H.aligned.map (fun P =>
    P.transport D S old L y hsep hcoset) ++
    [alignedNamedBoundaryFresh D S old L M R y hsep hcoset]
  refine
    { named := N
      aligned := boundaries
      blocksAgree := ?_ }
  change
    namedHistoricalStepList D S old L M R y hsep hcoset
      H.named.named =
    alignedBoundaryBlockSequence D S old L
      (namedHistoricalLast D S old L M
        (step D S old L R y hsep)
        (step_lastMaskCoset D S old L M R y hsep hcoset))
      (H.aligned.map (fun P =>
        P.transport D S old L y hsep hcoset) ++
        [alignedNamedBoundaryFresh D S old L M R y hsep hcoset])
  rw [H.blocksAgree]
  exact (alignedBoundaryBlockSequence_step
    D S old L M R y hsep hcoset H.aligned).symm

/-- Same exact pair/next/tail recursion as the manuscript,
now retaining the original covered named history and its
genuinely aligned boundary endpoint list simultaneously. -/
noncomputable def coveredNamedAlignedBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : CoveredNamedAlignedHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    CoveredNamedAlignedHistory D S old L M := by
  induction rest generalizing p c H with
  | nil => exact H
  | cons z zs ih =>
      have hstep :
          (match H.named.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coveredNamedAlignedStep D S old L M H z hstep
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- Every nonempty separated original LinkChain acquires the
coherent historical boundary list without replacing its
existing source-named, covered component history. -/
noncomputable def coveredNamedAlignedBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    CoveredNamedAlignedHistory D S old L M := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => exact coveredNamedAlignedInitial D S old L M x
      | cons y ys =>
          let H0 := coveredNamedAlignedInitial D S old L M x
          let H1 := coveredNamedAlignedStep D S old L M H0 y trivial
          have hp : H1.named.data.chain.previous = some x := rfl
          have hc : H1.named.data.chain.current = y := rfl
          exact coveredNamedAlignedBuildTail
            D S old L M x y H1 hp hc ys hsep

/-- Forgetting the boundary certificates along any finite tail
returns the identical previously verified named historical chain. -/
theorem coveredNamedAlignedBuildTail_named_eq
    (M : Proper S) (p c : Atom S old)
    (H : CoveredNamedAlignedHistory D S old L M)
    (hp : H.named.data.chain.previous = some p)
    (hc : H.named.data.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (coveredNamedAlignedBuildTail D S old L M
      p c H hp hc rest hsep).named =
    namedHistoryBuildTail D S old L M
      p c H.named hp hc rest hsep := by
  induction rest generalizing p c H with
  | nil => rfl
  | cons z zs ih =>
      have hstep :
          (match H.named.data.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous
                H.named.data.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := coveredNamedAlignedStep D S old L M H z hstep
      have hnp : HN.named.data.chain.previous = some c := by
        change some H.named.data.chain.current = some c
        rw [hc]
      have hnc : HN.named.data.chain.current = z := rfl
      change
        (coveredNamedAlignedBuildTail D S old L M
          c z HN hnp hnc zs hsep.2).named =
        namedHistoryBuildTail D S old L M
          c z HN.named hnp hnc zs hsep.2
      exact ih c z HN hnp hnc hsep.2

/-- The finite enhanced history is literally the previously
verified namedHistoryBuildNonempty dependent history after
forgetting only the extra aligned original boundary list. -/
theorem coveredNamedAlignedBuildNonempty_named_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (coveredNamedAlignedBuildNonempty D S old L M
      atoms hne hsep).named =
      namedHistoryBuildNonempty D S old L M
        atoms hne hsep := by
  cases atoms with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          let H0 := coveredNamedAlignedInitial D S old L M x
          let H1 := coveredNamedAlignedStep D S old L M H0 y trivial
          have hp : H1.named.data.chain.previous = some x := rfl
          have hc : H1.named.data.chain.current = y := rfl
          change
            (coveredNamedAlignedBuildTail D S old L M
              x y H1 hp hc ys hsep).named =
            namedHistoryBuildTail D S old L M
              x y H1.named hp hc ys hsep
          exact coveredNamedAlignedBuildTail_named_eq
            D S old L M x y H1 hp hc ys hsep

/-- FINITE BLOCK/BOUNDARY POSITIONAL CORRESPONDENCE in the
SAME already covered source-named history used by the
verified nonempty M-component active interval theorem.

There is no separately built quotient, equality cast or
missing identified source-mask occurrence. -/
theorem coveredNamedAlignedBuildNonempty_sameBlocks
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := coveredNamedAlignedBuildNonempty
      D S old L M atoms hne hsep
    H.named.named =
      alignedBoundaryBlockSequence D S old L
        (namedHistoricalLast D S old L M
          H.named.data.chain H.named.data.lastInv)
        H.aligned := by
  intro H
  exact H.blocksAgree

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
