import GluingEPPA.Steiner.ChainValuation.BoundaryHistoryOriginalCorrespondence

/-!
# Injection of the genuine parameter carriers of all historical boundaries

An embedded Cayley chart does not, on its own, establish that the
chosen parameterization of its interface is injective. The actual
LinkChain.step uses injective old Link homomorphisms and translation
on the left. Both parameter maps are therefore injective at the
moment of attachment. Historical transport does not modify them.

This proves the missing interface-monomorphism invariant through
every subsequent genuine separated attachment and finite recursion.
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

/-- Both original intersection-group parameterizations are injective. -/
def HistoricalLinkBoundary.ParametersInjective
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R) : Prop :=
  Function.Injective T.leftParam ∧
  Function.Injective T.rightParam

/-- Actual new attachment parameters are an injective Link map,
possibly preceded by translation by the current atom's shift. -/
theorem historicalLinkBoundary_step_parametersInjective
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R) :
    (historicalLinkBoundary_step D S old L M R y hsep hcoset).
      ParametersInjective D S old L := by
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi : Function.Injective i :=
    left_injective D S old L R.current.1 y.1
  have hj : Function.Injective j :=
    right_injective D S old L R.current.1 y.1
  constructor
  · intro k k' heq
    have hmul : R.current.2 * i k = R.current.2 * i k' := heq
    exact hi (mul_left_cancel hmul)
  · exact hj

/-- Historical transport changes only the two embeddings in the
current quotient; it does not change either parameter map. -/
theorem HistoricalLinkBoundary.transport_parametersInjective
    {M : Proper S} {R : BuildResult D S old L}
    (T : HistoricalLinkBoundary D S old L M R)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (hInj : T.ParametersInjective D S old L) :
    (T.transport D S old L y hsep hcoset).
      ParametersInjective D S old L := hInj

/-- All original Link intersection-group interfaces in a historical
boundary list remain injectively parameterized. -/
def HistoricalBoundariesParametersInjective
    (M : Proper S) (R : BuildResult D S old L)
    (boundaries : List (HistoricalLinkBoundary D S old L M R)) : Prop :=
  ∀ T, T ∈ boundaries → T.ParametersInjective D S old L

theorem historicalBoundaries_step_parametersInjective
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hcoset : LastMaskCoset D S old L M R)
    (boundaries : List (HistoricalLinkBoundary D S old L M R))
    (hOld : HistoricalBoundariesParametersInjective
      D S old L M R boundaries) :
    HistoricalBoundariesParametersInjective D S old L M
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
    exact U.transport_parametersInjective D S old L y hsep
      hcoset (hOld U hU)
  · have hEq :
        T = historicalLinkBoundary_step D S old L M R y hsep hcoset :=
      List.mem_singleton.mp hTnew
    subst T
    exact historicalLinkBoundary_step_parametersInjective
      D S old L M R y hsep hcoset

/-- The finite witnessed history has injectively parameterized
interfaces at each of its literal original consecutive boundaries. -/
theorem boundaryHistoryBuildNonempty_allParametersInjective
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := boundaryHistoryBuildNonempty D S old L M atoms hne hsep
    HistoricalBoundariesParametersInjective
      D S old L M H.chain H.boundaries := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          intro T hT
          simp [boundaryHistoryBuildNonempty, boundaryHistoryInitial,
            HistoricalBoundariesParametersInjective] at hT
      | cons y ys =>
          let H0 := boundaryHistoryInitial D S old L M x
          let H1 := boundaryHistoryStep D S old L M H0 y trivial
          have hp : H1.chain.previous = some x := rfl
          have hc : H1.chain.current = y := rfl
          have hInit :
              HistoricalBoundariesParametersInjective
                D S old L M H0.chain H0.boundaries := by
            intro T hT
            simp [H0, boundaryHistoryInitial] at hT
          have hFirst :
              HistoricalBoundariesParametersInjective
                D S old L M H1.chain H1.boundaries :=
            historicalBoundaries_step_parametersInjective
              D S old L M H0.chain y trivial H0.lastInv
              H0.boundaries hInit
          change HistoricalBoundariesParametersInjective
            D S old L M
            (boundaryHistoryBuildTail D S old L M x y H1 hp hc
              ys hsep).chain
            (boundaryHistoryBuildTail D S old L M x y H1 hp hc
              ys hsep).boundaries
          exact boundaryHistoryBuildTail_parametersInjective
            D S old L M x y H1 hp hc ys hsep hFirst

/-- The literal tail recursor preserves injectivity of all historical
parameter interfaces. -/
theorem boundaryHistoryBuildTail_parametersInjective
    (M : Proper S) (p c : Atom S old)
    (H : BoundaryHistoryBuildResult D S old L M)
    (hp : H.chain.previous = some p)
    (hc : H.chain.current = c)
    (rest : List (Atom S old))
    (hsep : separatedList D S old L (p :: c :: rest))
    (hOld : HistoricalBoundariesParametersInjective
      D S old L M H.chain H.boundaries) :
    let H' := boundaryHistoryBuildTail D S old L M p c H hp hc rest hsep
    HistoricalBoundariesParametersInjective
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
      change HistoricalBoundariesParametersInjective
        D S old L M
        (boundaryHistoryBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).chain
        (boundaryHistoryBuildTail D S old L M c z HN
          hnp hnc zs hsep.2).boundaries
      exact ih c z HN hnp hnc hsep.2
        (historicalBoundaries_step_parametersInjective
          D S old L M H.chain z hs H.lastInv
          H.boundaries hOld)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
