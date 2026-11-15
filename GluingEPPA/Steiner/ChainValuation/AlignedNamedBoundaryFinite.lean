import GluingEPPA.Steiner.ChainValuation.AlignedNamedBoundaryHistory
import GluingEPPA.Steiner.ChainValuation.BoundaryHistoryOriginalCorrespondence

/-!
# Every finite original Link chain has an aligned named-boundary history

Iterate the one-step chart-pairing record through precisely the
manuscript's one-, two-, and many-block LinkChain construction.
For every actual consecutive historical boundary retain:

* its genuine original earlier K_(A intersect B) interface record;
* the actual named left and right source Cayley block charts;
* equality of both source masks and both complete embedding ranges;
* the same original dependent chain quotient and point matchings.

The final forgetful equality identifies the complete certified list
with the previously checked boundary-history builder, and hence
with the literal original LinkChain.buildNonempty realization.

This is a global alignment theorem, not yet a normalized
proper-mask *component equivalence*. Selecting and coordinating
the M-coset representatives along an active interval is next.
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

/-- The exact actual separated tail, enriched with every named
left/right chart and its witnessed common interface. -/
noncomputable def alignedNamedBuildTail
    (M : Proper S) (p c : Atom S old)
    (H : AlignedNamedHistory D S old L M)
    (hp : H.boundaryHistory.chain.previous = some p)
    (hc : H.boundaryHistory.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    AlignedNamedHistory D S old L M := by
  induction rest generalizing p c H with
  | nil =>
      exact H
  | cons z zs ih =>
      have hstep :
          (match H.boundaryHistory.chain.previous with
           | none => True
           | some previous =>
               tripleSeparated D S old L previous
                 H.boundaryHistory.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := alignedNamedStep D S old L M H z hstep
      have hnp : HN.boundaryHistory.chain.previous = some c := by
        change some H.boundaryHistory.chain.current = some c
        rw [hc]
      have hnc : HN.boundaryHistory.chain.current = z := rfl
      exact ih c z HN hnp hnc hsep.2

/-- All historical boundaries of an arbitrary nonempty separated
list, simultaneously equipped with the original adjacent named
Cayley-block charts and exact range agreement. -/
noncomputable def alignedNamedBuildNonempty
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    AlignedNamedHistory D S old L M := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          exact alignedNamedInitial D S old L M x
      | cons y ys =>
          let H0 := alignedNamedInitial D S old L M x
          let H1 := alignedNamedStep D S old L M H0 y trivial
          have hp : H1.boundaryHistory.chain.previous = some x := rfl
          have hc : H1.boundaryHistory.chain.current = y := rfl
          exact alignedNamedBuildTail D S old L M x y H1 hp hc ys hsep

/-- Forgetting chart-pairing certificates along a tail gives the
exact same historical boundary builder on the same original state. -/
theorem alignedNamedBuildTail_boundary_eq
    (M : Proper S) (p c : Atom S old)
    (H : AlignedNamedHistory D S old L M)
    (hp : H.boundaryHistory.chain.previous = some p)
    (hc : H.boundaryHistory.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest)) :
    (alignedNamedBuildTail D S old L M p c H hp hc rest hsep).boundaryHistory =
      boundaryHistoryBuildTail D S old L M p c
        H.boundaryHistory hp hc rest hsep := by
  induction rest generalizing p c H with
  | nil => rfl
  | cons z zs ih =>
      have hstep :
          (match H.boundaryHistory.chain.previous with
           | none => True
           | some previous =>
               tripleSeparated D S old L previous
                 H.boundaryHistory.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := alignedNamedStep D S old L M H z hstep
      have hnp : HN.boundaryHistory.chain.previous = some c := by
        change some H.boundaryHistory.chain.current = some c
        rw [hc]
      have hnc : HN.boundaryHistory.chain.current = z := rfl
      change
        (alignedNamedBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).boundaryHistory =
        boundaryHistoryBuildTail D S old L M c z HN.boundaryHistory
          hnp hnc zs hsep.2
      exact ih c z HN hnp hnc hsep.2

/-- The entire enriched boundary history is literally the earlier
verified one, not an arbitrary point-set-equivalent replacement. -/
theorem alignedNamedBuildNonempty_boundary_eq
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    (alignedNamedBuildNonempty D S old L M atoms hne hsep).boundaryHistory =
      boundaryHistoryBuildNonempty D S old L M atoms hne hsep := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          let H0 := alignedNamedInitial D S old L M x
          let H1 := alignedNamedStep D S old L M H0 y trivial
          have hp : H1.boundaryHistory.chain.previous = some x := rfl
          have hc : H1.boundaryHistory.chain.current = y := rfl
          change
            (alignedNamedBuildTail D S old L M x y H1
              hp hc ys hsep).boundaryHistory =
            boundaryHistoryBuildTail D S old L M x y H1.boundaryHistory
              hp hc ys hsep
          exact alignedNamedBuildTail_boundary_eq
            D S old L M x y H1 hp hc ys hsep

/-- The enriched finite history has EXACTLY the original
manuscript's dependent SomeState: current source atom, quotient
carrier, and genuine completed matching families are unchanged. -/
theorem alignedNamedBuildNonempty_original
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := alignedNamedBuildNonempty D S old L M atoms hne hsep
    (⟨H.boundaryHistory.chain.current, H.boundaryHistory.chain.state⟩ :
      SomeState S old) =
      buildNonempty D S old L atoms hne hsep := by
  let H := alignedNamedBuildNonempty D S old L M atoms hne hsep
  have heq : H.boundaryHistory =
      boundaryHistoryBuildNonempty D S old L M atoms hne hsep :=
    alignedNamedBuildNonempty_boundary_eq
      D S old L M atoms hne hsep
  have hstate :
      (⟨H.boundaryHistory.chain.current,
         H.boundaryHistory.chain.state⟩ : SomeState S old) =
      (⟨(boundaryHistoryBuildNonempty D S old L M
          atoms hne hsep).chain.current,
         (boundaryHistoryBuildNonempty D S old L M
          atoms hne hsep).chain.state⟩ : SomeState S old) :=
    congrArg
      (fun T : BoundaryHistoryBuildResult D S old L M =>
        (⟨T.chain.current, T.chain.state⟩ : SomeState S old)) heq
  exact hstate.trans
    (boundaryHistoryBuildNonempty_original D S old L M atoms hne hsep)

/-- At every consecutive source-mask boundary of the exact original
finite chain, there is an explicit record pairing its genuine
interface with both actual adjacent named Cayley block charts.
Every record is furnished with exact source-mask and chart-range
agreement, and none of the original boundaries is lost. -/
theorem buildNonempty_has_aligned_named_boundaries
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    ∃ H : AlignedNamedHistory D S old L M,
      (⟨H.boundaryHistory.chain.current,
         H.boundaryHistory.chain.state⟩ : SomeState S old) =
        buildNonempty D S old L atoms hne hsep ∧
      H.aligned.map (fun P =>
        (P.boundary.leftMask, P.boundary.rightMask)) =
        consecutiveSourceMaskPairs S old atoms ∧
      H.aligned.map (fun P => P.boundary) =
        H.boundaryHistory.boundaries := by
  let H := alignedNamedBuildNonempty D S old L M atoms hne hsep
  refine ⟨H, ?_, ?_, H.forget⟩
  · exact alignedNamedBuildNonempty_original
      D S old L M atoms hne hsep
  · calc
      H.aligned.map (fun P =>
          (P.boundary.leftMask, P.boundary.rightMask)) =
          (H.aligned.map (fun P => P.boundary)).map
            (fun P => (P.leftMask, P.rightMask)) := by
        simp only [List.map_map, Function.comp_def]
      _ = H.boundaryHistory.boundaries.map
            (fun P => (P.leftMask, P.rightMask)) := by
        rw [H.forget]
      _ = consecutiveSourceMaskPairs S old atoms := by
        rw [alignedNamedBuildNonempty_boundary_eq
          D S old L M atoms hne hsep]
        exact boundaryHistoryBuildNonempty_sourcePairs
          D S old L M atoms hne hsep

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
