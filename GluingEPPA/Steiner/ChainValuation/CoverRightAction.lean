import GluingEPPA.Steiner.ChainValuation.EquivariantTestCovers

/-!
# Right actions obtained from equivariant test covers

The source word relations and the cover hypotheses are explicit inputs.
This connects the checked cover transfer to `wordRightAction`, whose
output has the form required for the extra test actions in
`AugmentedStep.inclusion`. It does not construct covers of chain tests.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace ChainValuation

universe u v w z
variable {E : Type u} {X : Type v} {J : Type z} {M : Finset E}
variable (A : Data E M) (W : J → Type w)
variable (σ : ∀ j : J, E → Equiv.Perm (W j))
variable (τ : E → Equiv.Perm X) (f : ∀ j : J, W j → X)
variable (hcover : ∀ x : X, ∃ j : J, ∃ y : W j, f j y = x)
variable (hmap : ∀ j e, e ∈ M → ∀ y, f j (σ j e y) = τ e (f j y))
variable (hsource : ∀ j (p q : List E),
  (∀ e ∈ p, e ∈ M) → (∀ e ∈ q, e ∈ M) →
  (p.map A.edge).prod = (q.map A.edge).prod →
  testWordPerm (σ j) p = testWordPerm (σ j) q)

include hcover hmap hsource

/-- Every relation in the earlier group acts identically on the covered test. -/
theorem coveredTest_kernel (p q : List E)
    (hp : ∀ e ∈ p, e ∈ M) (hq : ∀ e ∈ q, e ∈ M)
    (heq : (p.map A.edge).prod = (q.map A.edge).prod) :
    testWordPerm τ p = testWordPerm τ q := by
  exact testWordPerm_eq_of_joint_equivariant_cover
    W σ τ M f hcover hmap p q hp hq
    (fun j => hsource j p q hp hq heq)

/-- The concrete earlier-group action induced on a jointly covered test. -/
noncomputable def rightActionOfEquivariantCover : RightAction A.Carrier X :=
  wordRightAction A τ
    (coveredTest_kernel A W σ τ f hcover hmap hsource)

/-- This action gives exactly the prescribed completed letter permutations. -/
theorem rightActionOfEquivariantCover_edge (e : E) (he : e ∈ M) (x : X) :
    (rightActionOfEquivariantCover A W σ τ f hcover hmap hsource).act
      x (A.edge e) = τ e x := by
  exact wordRightAction_edge A τ
    (coveredTest_kernel A W σ τ f hcover hmap hsource) e he x

/-- Reading an allowed word agrees with the original permutation test. -/
theorem rightActionOfEquivariantCover_word
    (word : List E) (hword : ∀ e ∈ word, e ∈ M) (x : X) :
    (rightActionOfEquivariantCover A W σ τ f hcover hmap hsource).act
      x ((word.map A.edge).prod) = testWordPerm τ word x := by
  exact wordActionValue_word A τ
    (coveredTest_kernel A W σ τ f hcover hmap hsource) word hword x

end ChainValuation
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
