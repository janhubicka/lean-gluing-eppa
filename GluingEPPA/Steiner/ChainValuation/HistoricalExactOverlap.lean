import GluingEPPA.Steiner.ChainValuation.HistoricalBoundaryParameterInjectivity

/-!
# Every genuine historical Link interface has exactly one gluing parameter

A historical boundary's reachability iff is not the same as an
*equality-of-points* iff. In an actual injective LinkChain pushout,
the latter is stronger: old and new source points are literally
identified precisely when both are images of one original parameter
k in K_(A ∩ B). This is an exact overlap, not an M-path statement.

We prove the assertion at the original attachment, transport it
through every later injective old-chain embedding, and iterate it
over the finite separated-list builder. Together with injectivity
of the boundary parameter maps, the witnessing k is unique.

This module is independent of the still missing all-length
normalized M-component isomorphism.
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

/-- Equality of actual quotient points across a historical boundary
comes from a parameter of the *original* intersection group.
This is stronger than the already recorded M-reachability law. -/
def HistoricalLinkBoundary.ExactOverlap
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R) : Prop :=
  ∀ x y, T.leftChart x = T.rightChart y ↔
    ∃ k : (old (common S T.leftMask T.rightMask)).Carrier,
      T.leftParam k = x ∧ T.rightParam k = y

/-- For the newly attached literal Link blocks, exact overlap follows
from the injective pushout's cross-side equality criterion and the
old chain's injective final-block chart. -/
theorem historicalLinkBoundary_step_exactOverlap
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (historicalLinkBoundary_step D S old L M R y hsep hcoset).
      ExactOverlap D S old L := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi : Function.Injective i :=
    left_injective D S old L R.current.1 y.1
  have hj : Function.Injective j :=
    right_injective D S old L R.current.1 y.1
  intro x z
  change
    oldEmbed A B R.state R.current.2 i j hi hj (R.state.lastEmbed x) =
      newEmbed A B R.state R.current.2 i j hi hj z ↔
      ∃ k : (old (common S R.current.1 y.1)).Carrier,
        R.current.2 * i k = x ∧ j k = z
  constructor
  · intro h
    obtain ⟨k, hx, hz⟩ :=
      (oldEmbed_eq_newEmbed_iff A B R.state R.current.2
        i j hi hj (R.state.lastEmbed x) z).mp h
    exact ⟨k, R.state.lastInjective hx, hz⟩
  · rintro ⟨k, hx, hz⟩
    apply (oldEmbed_eq_newEmbed_iff A B R.state R.current.2
      i j hi hj (R.state.lastEmbed x) z).mpr
    exact ⟨k, congrArg R.state.lastEmbed hx, hz⟩

/-- A later separated Link step embeds the entire old quotient
injectively. Therefore it cannot introduce new equalities between
any two original Cayley charts of a previously recorded boundary. -/
theorem HistoricalLinkBoundary.transport_exactOverlap
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (hExact : T.ExactOverlap D S old L) :
    (T.transport D S old L y hsep hcoset).
      ExactOverlap D S old L := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi : Function.Injective i :=
    left_injective D S old L R.current.1 y.1
  have hj : Function.Injective j :=
    right_injective D S old L R.current.1 y.1
  intro x z
  change
    oldEmbed A B R.state R.current.2 i j hi hj (T.leftChart x) =
      oldEmbed A B R.state R.current.2 i j hi hj (T.rightChart z) ↔
      ∃ k : (old (common S T.leftMask T.rightMask)).Carrier,
        T.leftParam k = x ∧ T.rightParam k = z
  constructor
  · intro h
    exact (hExact x z).mp
      ((oldEmbed_injective A B R.state R.current.2 i j hi hj) h)
  · intro h
    exact congrArg (oldEmbed A B R.state R.current.2 i j hi hj)
      ((hExact x z).mpr h)

/-- All boundaries of one concrete historical list have exact
cross-side point overlap, not merely a reachability witness. -/
def HistoricalBoundariesExactOverlap
    (M : Proper S) (R : BuildResult D S old L)
    (boundaries : List (HistoricalLinkBoundary D S old L M R)) : Prop :=
  ∀ T, T ∈ boundaries → T.ExactOverlap D S old L

theorem historicalBoundaries_step_exactOverlap
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (boundaries : List (HistoricalLinkBoundary D S old L M R))
    (hOld : HistoricalBoundariesExactOverlap D S old L M R boundaries) :
    HistoricalBoundariesExactOverlap D S old L M
      (step D S old L R y hsep)
      (historicalBoundaries_step D S old L M R y hsep hcoset
        boundaries) := by
  intro T hT
  have hmem :
      T ∈ boundaries.map (fun B =>
        B.transport D S old L y hsep hcoset) ++
        [historicalLinkBoundary_step D S old L M R y hsep hcoset] := hT
  rcases List.mem_append.mp hmem with hTold | hTnew
  · obtain ⟨U, hU, hEq⟩ := List.mem_map.mp hTold
    subst T
    exact U.transport_exactOverlap D S old L y hsep hcoset
      (hOld U hU)
  · have hEq :
        T = historicalLinkBoundary_step D S old L M R y hsep hcoset :=
      List.mem_singleton.mp hTnew
    subst T
    exact historicalLinkBoundary_step_exactOverlap
      D S old L M R y hsep hcoset

theorem boundaryHistoryBuildTail_exactOverlap
    (M : Proper S) (p c : Atom S old)
    (H : BoundaryHistoryBuildResult D S old L M)
    (hp : H.chain.previous = some p)
    (hc : H.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest))
    (hOld : HistoricalBoundariesExactOverlap
      D S old L M H.chain H.boundaries) :
    let H' := boundaryHistoryBuildTail D S old L M p c H hp hc rest hsep
    HistoricalBoundariesExactOverlap
      D S old L M H'.chain H'.boundaries := by
  induction rest generalizing p c H with
  | nil =>
      exact hOld
  | cons z zs ih =>
      have hs :
          (match H.chain.previous with
          | none => True
          | some previous =>
              tripleSeparated D S old L previous H.chain.current z) := by
        rw [hp, hc]
        exact hsep.1
      let HN := boundaryHistoryStep D S old L M H z hs
      have hnp : HN.chain.previous = some c := by
        change some H.chain.current = some c
        rw [hc]
      have hnc : HN.chain.current = z := rfl
      change HistoricalBoundariesExactOverlap
        D S old L M
        (boundaryHistoryBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).chain
        (boundaryHistoryBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).boundaries
      exact ih c z HN hnp hnc hsep.2
        (historicalBoundaries_step_exactOverlap
          D S old L M H.chain z hs H.lastInv
          H.boundaries hOld)

theorem boundaryHistoryBuildNonempty_allExactOverlap
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := boundaryHistoryBuildNonempty D S old L M atoms hne hsep
    HistoricalBoundariesExactOverlap
      D S old L M H.chain H.boundaries := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          intro T hT
          simp [boundaryHistoryBuildNonempty, boundaryHistoryInitial,
            HistoricalBoundariesExactOverlap] at hT
      | cons y ys =>
          let H0 := boundaryHistoryInitial D S old L M x
          let H1 := boundaryHistoryStep D S old L M H0 y trivial
          have hp : H1.chain.previous = some x := rfl
          have hc : H1.chain.current = y := rfl
          have hInit :
              HistoricalBoundariesExactOverlap
                D S old L M H0.chain H0.boundaries := by
            intro T hT
            simp [H0, boundaryHistoryInitial] at hT
          have hFirst :
              HistoricalBoundariesExactOverlap
                D S old L M H1.chain H1.boundaries :=
            historicalBoundaries_step_exactOverlap
              D S old L M H0.chain y trivial H0.lastInv
              H0.boundaries hInit
          change HistoricalBoundariesExactOverlap
            D S old L M
            (boundaryHistoryBuildTail D S old L M x y H1 hp hc
              ys hsep).chain
            (boundaryHistoryBuildTail D S old L M x y H1 hp hc
              ys hsep).boundaries
          exact boundaryHistoryBuildTail_exactOverlap
            D S old L M x y H1 hp hc ys hsep hFirst

/-- An exact cross-side point equality has a unique witness from the
original intersection group, because its parameterization is
injective. There is no M-connectivity hypothesis in this statement. -/
theorem HistoricalLinkBoundary.uniqueOverlap
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (hExact : T.ExactOverlap D S old L)
    (hParam : T.ParametersInjective D S old L)
    (x : (old T.leftMask).Carrier) (y : (old T.rightMask).Carrier) :
    T.leftChart x = T.rightChart y ↔
      ∃! k : (old (common S T.leftMask T.rightMask)).Carrier,
        T.leftParam k = x ∧ T.rightParam k = y := by
  constructor
  · intro h
    obtain ⟨k, hx, hy⟩ := (hExact x y).mp h
    refine ⟨k, ⟨hx, hy⟩, ?_⟩
    intro k' hk'
    exact hParam.1 (hk'.1.trans hx.symm)
  · rintro ⟨k, ⟨hx, hy⟩, _⟩
    exact (hExact x y).mpr ⟨k, hx, hy⟩

/-- The *original* finite separated LinkChain.buildNonempty quotient
admits a historical boundary package containing exactly the
consecutive input source masks; every such actual boundary has a
unique intersection-group parameter for each equality of points. -/
theorem buildNonempty_has_unique_actual_boundaries
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    ∃ H : BoundaryHistoryBuildResult D S old L M,
      (⟨H.chain.current, H.chain.state⟩ : SomeState S old) =
        buildNonempty D S old L atoms hne hsep ∧
      H.boundaries.map (fun T => (T.leftMask, T.rightMask)) =
        consecutiveSourceMaskPairs S old atoms ∧
      (∀ T : HistoricalLinkBoundary D S old L M H.chain,
        T ∈ H.boundaries →
          T.Embeds D S old L ∧
          ∀ x y, T.leftChart x = T.rightChart y ↔
            ∃! k : (old (common S T.leftMask T.rightMask)).Carrier,
              T.leftParam k = x ∧ T.rightParam k = y) := by
  let H := boundaryHistoryBuildNonempty D S old L M atoms hne hsep
  refine ⟨H, ?_, ?_, ?_⟩
  · exact boundaryHistoryBuildNonempty_original D S old L M atoms hne hsep
  · exact boundaryHistoryBuildNonempty_sourcePairs D S old L M atoms hne hsep
  · intro T hT
    constructor
    · exact boundaryHistoryBuildNonempty_allEmbedded
        D S old L M atoms hne hsep T hT
    · exact T.uniqueOverlap D S old L
        (boundaryHistoryBuildNonempty_allExactOverlap
          D S old L M atoms hne hsep T hT)
        (boundaryHistoryBuildNonempty_allParametersInjective
          D S old L M atoms hne hsep T hT)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
