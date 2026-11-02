import GluingEPPA.Steiner.ChainValuation.AugmentedRecord

/-!
# One augmented recursive valuation step

This packages the old direct record plus arbitrary finite involutive test
coordinates into the same RecursiveRecord.Data interface used by the verified
Steiner recursion. Chain tests will later instantiate the extra coordinates.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace AugmentedStep

attribute [local instance] Classical.propDecidable

universe u
variable {V E J : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (X : J → Type u) [Finite J] [∀ j, Finite (X j)]
variable (τ : ∀ j, E → Equiv.Perm (X j))
variable (hτ : ∀ j e, τ j e * τ j e = 1)

/-- The parameterized step has exactly the old record coordinates, followed by
the supplied finite permutation tests. -/
noncomputable def data : Data E S where
  Carrier := AugmentedRecord.imageGroup D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ (S : Set E)
  group := inferInstance
  finite := inferInstance
  edge := AugmentedRecord.totalGenerator D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ (S : Set E)
  square := AugmentedRecord.totalGenerator_square D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ (S : Set E)
  outside := AugmentedRecord.totalGenerator_not_mem D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ (S : Set E)
  generated := AugmentedRecord.image_generated D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ (S : Set E)

/-- Forgetting the added test coordinates maps the augmented stage onto the
literal old direct record formed from the same proper stages. -/
noncomputable def forget :
    (data D S old X τ hτ).Carrier →*
      (Step.data D S old).Carrier :=
  AugmentedRecord.forget D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ (S : Set E)

/-- The forgetful map preserves every named generator in the current alphabet. -/
theorem forget_edge (e : E) (he : e ∈ S) :
    forget D S old X τ hτ ((data D S old X τ hτ).edge e) =
      (Step.data D S old).edge e := by
  change AugmentedRecord.forget D
      (Step.sets S) (Step.groups S old)
      (Step.edges S old) (Step.involutions S old)
      X τ hτ (S : Set E)
      (AugmentedRecord.totalGenerator D
        (Step.sets S) (Step.groups S old)
        (Step.edges S old) (Step.involutions S old)
        X τ hτ (S : Set E) e) =
    DirectRecord.totalGenerator D
      (Step.sets S) (Step.groups S old)
      (Step.edges S old) (Step.involutions S old)
      (S : Set E) e
  rw [AugmentedRecord.totalGenerator_mem _ _ _ _ _ _ _ _ e he,
    DirectRecord.totalGenerator_mem _ _ _ _ _ _ e he]
  rfl

end AugmentedStep
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
