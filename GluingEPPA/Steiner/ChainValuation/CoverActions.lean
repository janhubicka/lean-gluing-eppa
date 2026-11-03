import GluingEPPA.Steiner.ChainValuation.EquivariantCover
import GluingEPPA.Steiner.ChainValuation.AugmentedLinks

/-!
# The augmented recursive Link from equivariant covers of its test summands

For the chain-restriction induction, exact isomorphisms of every restricted
component are stronger than necessary. A surjective cover by earlier test
spaces, equivariant for every smaller-mask edge, already ensures that the
earlier group acts on the new tests. This file packages precisely that weaker
hypothesis and supplies an actual RecursiveRecord.Link, including deletion
and endpoint repair, with no new axioms.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

attribute [local instance] Classical.propDecidable

universe u
variable {E : Type u}

/-- A family of earlier tests covering one new test equivariantly. -/
structure TestCover (S : Finset E) (A : Data E S)
    (X : Type u) (τ : E → Equiv.Perm X) where
  Index : Type u
  Space : Index → Type u
  σ : ∀ i : Index, E → Equiv.Perm (Space i)
  f : ∀ i : Index, Space i → X
  surj : ∀ x : X, ∃ i : Index, ∃ y : Space i, f i y = x
  edge : ∀ i e, e ∈ S → ∀ y,
    f i ((σ i e) y) = τ e (f i y)
  words : ∀ (i : Index) (p q : List E),
    (∀ e ∈ p, e ∈ S) → (∀ e ∈ q, e ∈ S) →
    (p.map A.edge).prod = (q.map A.edge).prod →
    testWordPerm (σ i) p = testWordPerm (σ i) q

/-- Every equivariant covering supplies the actual group action needed by
the augmented recursive inclusion. -/
noncomputable def TestCover.rightAction
    {S : Finset E} {A : Data E S} {X : Type u}
    {τ : E → Equiv.Perm X} (C : TestCover S A X τ) :
    RightAction A.Carrier X :=
  rightAction_of_equivariantCover τ C.σ C.f A C.surj C.edge C.words

theorem TestCover.rightAction_edge
    {S : Finset E} {A : Data E S} {X : Type u}
    {τ : E → Equiv.Perm X} (C : TestCover S A X τ)
    (e : E) (he : e ∈ S) (x : X) :
    C.rightAction.act x (A.edge e) = τ e x :=
  rightAction_of_equivariantCover_edge τ C.σ C.f A C.surj C.edge
    C.words e he x

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
