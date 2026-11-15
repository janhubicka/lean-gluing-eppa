import GluingEPPA.Steiner.ChainValuation.AlignedNamedBoundaryFinite
import GluingEPPA.Steiner.ChainValuation.HistoricalInterfaceEquivalence

/-!
# Genuine interface parameters from adjacent active named components

A normalized proper-mask interval must select one actual parameter
in K_(A intersect B) for each pair of consecutive historical
blocks touched by the chosen M-component.

The globally aligned finite boundary history already identifies
the two named Cayley block chart images with the actual boundary
chart images. The previously checked historical-interface lemma
then yields an exact criterion: the component meets BOTH named
adjacent block charts if and only if it meets the literal original
common-interface image.

This converts active support bits into explicit genuine attaching
parameters, without postulating that two arbitrary selected cosets
meet or choosing an ambient top-stage group.
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

/-- Every *literal* common-interface point of an aligned boundary
lies in both named Cayley source-block images inside the actual
chain quotient. The coordinate witnesses need not be equal or
commute: only the two embedded images are identified. -/
theorem AlignedNamedBoundary.interface_has_named_endpoints
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (k : (old (common S P.boundary.leftMask
        P.boundary.rightMask)).Carrier) :
    (∃ x : (old P.leftNamed.source).Carrier,
      P.leftNamed.chart.embed x =
        P.boundary.interfaceMap D S old L k) ∧
    (∃ y : (old P.rightNamed.source).Carrier,
      P.rightNamed.chart.embed y =
        P.boundary.interfaceMap D S old L k) := by
  have hLeft :
      P.boundary.interfaceMap D S old L k ∈
        Set.range P.boundary.leftChart :=
    ⟨P.boundary.leftParam k, rfl⟩
  have hRight :
      P.boundary.interfaceMap D S old L k ∈
        Set.range P.boundary.rightChart :=
    ⟨P.boundary.rightParam k,
      (P.boundary.interfaceMap_eq_right D S old L k).symm⟩
  constructor
  · rw [P.agree.2.2.1] at hLeft
    exact hLeft
  · rw [P.agree.2.2.2] at hRight
    exact hRight

/-- A genuine M-component meets an actual original interface iff
it meets *both* adjacent named Cayley charts of that interface.
All reachability is in the original completed matching quotient.

The reverse direction is the essential one: it produces a real
K_(A intersect B) parameter from two separately named historical
support witnesses, rather than assuming a gluing point. -/
theorem AlignedNamedBoundary.meets_interface_iff_named
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (q : R.state.Space) :
    (∃ k : (old (common S P.boundary.leftMask
        P.boundary.rightMask)).Carrier,
      LabelReach (fun e => (R.state.matching e).Rel) M.val
        q (P.boundary.interfaceMap D S old L k)) ↔
    (∃ x : (old P.leftNamed.source).Carrier,
      LabelReach (fun e => (R.state.matching e).Rel) M.val
        q (P.leftNamed.chart.embed x)) ∧
    (∃ y : (old P.rightNamed.source).Carrier,
      LabelReach (fun e => (R.state.matching e).Rel) M.val
        q (P.rightNamed.chart.embed y)) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ :=
      P.interface_has_named_endpoints D S old L k
    constructor
    · refine ⟨x, ?_⟩
      rw [hx]
      exact hk
    · refine ⟨y, ?_⟩
      rw [hy]
      exact hk
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hLeftRange :
        P.leftNamed.chart.embed x ∈
          Set.range P.boundary.leftChart := by
      rw [P.agree.2.2.1]
      exact ⟨x, rfl⟩
    have hRightRange :
        P.rightNamed.chart.embed y ∈
          Set.range P.boundary.rightChart := by
      rw [P.agree.2.2.2]
      exact ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hLeftRange
    obtain ⟨b, hb⟩ := hRightRange
    have hLeft :
        LabelReach (fun e => (R.state.matching e).Rel) M.val
          q (P.boundary.leftChart a) := by
      rw [ha]
      exact hx
    have hRight :
        LabelReach (fun e => (R.state.matching e).Rel) M.val
          q (P.boundary.rightChart b) := by
      rw [hb]
      exact hy
    exact P.boundary.component_meets_interface
      D S old L q ⟨a, hLeft⟩ ⟨b, hRight⟩

/-- The complete original finite LinkChain provides this exact
interface parameter criterion for EVERY one of its true consecutive
historical boundaries, with its two actual named block charts. -/
theorem alignedNamedBuildNonempty_all_interface_witnesses
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := alignedNamedBuildNonempty D S old L M atoms hne hsep
    ∀ (P : AlignedNamedBoundary D S old L M H.boundaryHistory.chain),
      P ∈ H.aligned →
      ∀ q : H.boundaryHistory.chain.state.Space,
        (∃ k : (old (common S P.boundary.leftMask
            P.boundary.rightMask)).Carrier,
          LabelReach
            (fun e => (H.boundaryHistory.chain.state.matching e).Rel)
            M.val q (P.boundary.interfaceMap D S old L k)) ↔
        (∃ x : (old P.leftNamed.source).Carrier,
          LabelReach
            (fun e => (H.boundaryHistory.chain.state.matching e).Rel)
            M.val q (P.leftNamed.chart.embed x)) ∧
        (∃ y : (old P.rightNamed.source).Carrier,
          LabelReach
            (fun e => (H.boundaryHistory.chain.state.matching e).Rel)
            M.val q (P.rightNamed.chart.embed y)) := by
  intro H P _ q
  exact P.meets_interface_iff_named D S old L q

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
