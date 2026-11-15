import GluingEPPA.Steiner.ChainValuation.AlignedNamedBoundaryComponentWitness

/-!
# Simultaneous genuine interface parameters for any selected active interval

Once the historical block support interval is known, the finite
normalization must choose a parameter at EVERY boundary of that
interval. The sets of parameters depend on the two adjacent
original source masks, so a uniform family of one ambient-group
parameters would be incorrect.

This module keeps the original ordered list of selected actual
aligned Link boundaries, together with explicit proofs that each
boundary belongs to the certified original history and that the
chosen M-component meets both named sides. It then constructs,
simultaneously, one real parameter in the appropriate genuine
earlier K_(A intersect B) at each selected position.

The construction preserves list length and duplicates. It makes
no assumption that the original masks are distinct, and does not
claim that an arbitrary selected list is already a consecutive
active interval: that is supplied separately by the verified
historical-support theorem.
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

/-- Both genuine named historical source-block charts of one
original interface are reached by the selected actual M-component. -/
def AlignedNamedBoundary.BothSidesActive
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (q : R.state.Space) : Prop :=
  (∃ x : (old P.leftNamed.source).Carrier,
    LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (P.leftNamed.chart.embed x)) ∧
  (∃ y : (old P.rightNamed.source).Carrier,
    LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (P.rightNamed.chart.embed y))

/-- One actual common-group parameter of an original historical
interface, with proof that its point is in the chosen M-component. -/
structure AlignedNamedBoundary.InterfaceChoice
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (q : R.state.Space) where
  parameter : (old (common S P.boundary.leftMask
    P.boundary.rightMask)).Carrier
  reached : LabelReach (fun e => (R.state.matching e).Rel) M.val
    q (P.boundary.interfaceMap D S old L parameter)

/-- The exact interface criterion produces an actual parameter,
with no arbitrary assumption that the two selected cosets intersect. -/
noncomputable def AlignedNamedBoundary.chooseInterface
    {M : Proper S} {R : BuildResult D S old L}
    (P : AlignedNamedBoundary D S old L M R)
    (q : R.state.Space)
    (h : P.BothSidesActive D S old L q) :
    P.InterfaceChoice D S old L q := by
  -- Eliminating an existential proof directly into this Type-valued
  -- certificate is not permitted; use finite classical choice.
  have hex : ∃ k : (old (common S P.boundary.leftMask
      P.boundary.rightMask)).Carrier,
      LabelReach (fun e => (R.state.matching e).Rel) M.val
        q (P.boundary.interfaceMap D S old L k) :=
    (P.meets_interface_iff_named D S old L q).mpr h
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

/-- A list of selected true historical interfaces, in its original
order and with repetition retained, whose both named source blocks
meet the same actual M-component. A later proof identifies this
list with the consecutive active support interval. -/
structure ActiveBoundarySelection
    (M : Proper S)
    (H : AlignedNamedHistory D S old L M)
    (q : H.boundaryHistory.chain.state.Space) where
  boundaries : List
    (AlignedNamedBoundary D S old L M H.boundaryHistory.chain)
  historical : ∀ P, P ∈ boundaries → P ∈ H.aligned
  active : ∀ P, P ∈ boundaries → P.BothSidesActive D S old L q

/-- Simultaneously choose an actual original K_(A∩B) parameter
at every selected historical boundary. The result is a LIST of
dependent pairs rather than parameters in an invented common group;
there is one entry for each original occurrence, including repeats. -/
noncomputable def ActiveBoundarySelection.chosenInterfaces
    {M : Proper S} {H : AlignedNamedHistory D S old L M}
    {q : H.boundaryHistory.chain.state.Space}
    (B : ActiveBoundarySelection D S old L M H q) :
    List (Σ P : AlignedNamedBoundary D S old L M H.boundaryHistory.chain,
      P.InterfaceChoice D S old L q) :=
  B.boundaries.attach.map (fun P =>
    ⟨P.val, P.val.chooseInterface D S old L q
      (B.active P.val P.property)⟩)

/-- The choice of actual dependent group parameters does not
lose or duplicate boundaries; this preserves the length bound
in the normalized smaller-chain test. -/
theorem ActiveBoundarySelection.chosenInterfaces_length
    {M : Proper S} {H : AlignedNamedHistory D S old L M}
    {q : H.boundaryHistory.chain.state.Space}
    (B : ActiveBoundarySelection D S old L M H q) :
    (B.chosenInterfaces D S old L).length = B.boundaries.length := by
  simp [ActiveBoundarySelection.chosenInterfaces]

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
