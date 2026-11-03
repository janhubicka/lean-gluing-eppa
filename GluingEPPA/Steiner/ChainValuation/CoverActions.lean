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

namespace AugmentedStep

universe u
variable {V E J : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ k : Proper S, Data E k.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))
variable (A : ∀ n m : Proper S, n.val ⊂ m.val →
  RightAction (old m).Carrier (Step.components D S old n))
variable (hA : ∀ (n m : Proper S) (h : n.val ⊂ m.val) e, e ∈ m.val → ∀ c,
  (A n m h).act c ((old m).edge e) =
    D.componentEdgePerm (Step.sets S n) (Step.edges S old n)
      (Step.involutions S old n) e c)
variable (X : J → Type u) [Finite J] [∀ j, Finite (X j)]
variable (τ : ∀ j, E → Equiv.Perm (X j))
variable (hτ : ∀ j e, τ j e * τ j e = 1)
variable (covers : ∀ (k : Proper S) (j : J),
  ChainValuation.TestCover k.val (old k) (X j) (τ j))

/-- Earlier compatible covers give a genuine augmented recursive Link.
The graph-theoretic existence of the covers is the remaining induction
problem, not an additional assumption in the final target theorem. -/
noncomputable def linkFromCovers (k : Proper S) :
    Link D (old k) (data D S old X τ hτ) :=
  link D S old L A hA X τ hτ
    (fun k j => (covers k j).rightAction)
    (by
      intro k j e he x
      exact (covers k j).rightAction_edge e he x)
    k

/-- Hence endpoint repair follows from the cover property, not from a
separate higher-acyclicity existence hypothesis. -/
theorem linkFromCovers_replace
    (k : Proper S) (s t : V) (g : (old k).Carrier)
    (p : D.WalkValue (S : Set E) (data D S old X τ hτ).edge s t
      ((linkFromCovers D S old L A hA X τ hτ covers k).incl g)) :
    D.WalkValue (Step.sets S k) (Step.edges S old k) s t g :=
  (linkFromCovers D S old L A hA X τ hτ covers k).replace s t g p

end AugmentedStep
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
