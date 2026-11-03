import GluingEPPA.Steiner.RecursiveLinks
import GluingEPPA.Steiner.ChainValuation.AugmentedStep
import GluingEPPA.Steiner.ChainValuation.AugmentedInclusion

/-!
# The verified old-link argument extends to augmented finite test coordinates

The only additional hypothesis is a right action of each proper-mask group
on every new finite test, with the prescribed generator permutations.  The
old component-record actions and the endpoint-repair proof are reused without
modification.  The chain-restriction theorem must supply the extra actions;
this file does not assume, or prove, that theorem.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace AugmentedStep

attribute [local instance] Classical.propDecidable

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
variable (B : ∀ k : Proper S, ∀ j : J,
  RightAction (old k).Carrier (X j))
variable (hB : ∀ k j e, e ∈ k.val → ∀ x,
  (B k j).act x ((old k).edge e) = τ j e x)

/-- The inclusion obtained by adjoining compatible test actions to the
old direct-record homomorphism. -/
noncomputable def inclusion (k : Proper S) :
    (old k).Carrier →* (data D S old X τ hτ).Carrier :=
  AugmentedRecord.inclusion D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ k (Step.hom D S old L A k) (B k)
    (S : Set E) k.property.1 (old k).generated
    (Step.hom_edge D S old L A hA k) (hB k)

/-- The augmented inclusion still sends each allowed generator to the
corresponding named generator of the new group. -/
theorem inclusion_edge (k : Proper S) (e : E) (he : e ∈ k.val) :
    inclusion D S old L A hA X τ hτ B hB k ((old k).edge e) =
      (data D S old X τ hτ).edge e := by
  apply Subtype.ext
  change AugmentedRecord.coordinateHom D
      (Step.sets S) (Step.groups S old)
      (Step.edges S old) (Step.involutions S old)
      X k (Step.hom D S old L A k) (B k) ((old k).edge e) =
    (AugmentedRecord.totalGenerator D
      (Step.sets S) (Step.groups S old)
      (Step.edges S old) (Step.involutions S old)
      X τ hτ (S : Set E) e).val
  rw [AugmentedRecord.totalGenerator_mem D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ (S : Set E) e (k.property.1 he)]
  exact AugmentedRecord.coordinateHom_generator D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ k (Step.hom D S old L A k) (B k)
    (Step.hom_edge D S old L A hA k) (hB k) e he

/-- Deletion is the old group-coordinate projection after forgetting the
new permutation tests. -/
noncomputable def deletion (k : Proper S) :
    (data D S old X τ hτ).Carrier →* (old k).Carrier :=
  (Step.projection D S old k).comp (forget D S old X τ hτ)

theorem deletion_edge (k : Proper S) (e : E) (he : e ∈ S) :
    deletion D S old X τ hτ k ((data D S old X τ hτ).edge e) =
      if e ∈ k.val then (old k).edge e else 1 := by
  change (Step.projection D S old k)
      (forget D S old X τ hτ ((data D S old X τ hτ).edge e)) = _
  rw [forget_edge D S old X τ hτ e]
  exact Step.projection_edge D S old k e he

/-- The manuscript's exact endpoint repair is inherited from its old
component record; the extra tests only refine equality of words. -/
theorem inclusion_replace
    (k : Proper S) (u v : V) (g : (old k).Carrier)
    (p : D.WalkValue (S : Set E) (data D S old X τ hτ).edge u v
      (inclusion D S old L A hA X τ hτ B hB k g)) :
    D.WalkValue (Step.sets S k) (Step.edges S old k) u v g := by
  obtain ⟨w, pw, hv⟩ := p.exists_word
  have hw := wordWalk_letters D pw
  have hval : AugmentedRecord.valuation D
      (Step.sets S) (Step.groups S old)
      (Step.edges S old) (Step.involutions S old)
      X τ hτ (S : Set E) w hw =
      inclusion D S old L A hA X τ hτ B hB k g := by
    rw [AugmentedRecord.valuation_eq_product]
    exact hv
  exact AugmentedRecord.inclusion_replacement D
    (Step.sets S) (Step.groups S old)
    (Step.edges S old) (Step.involutions S old)
    X τ hτ k (Step.hom D S old L A k) (B k)
    (S : Set E) k.property.1 (old k).generated
    (Step.hom_edge D S old L A hA k) (hB k)
    w hw pw g hval

/-- All three pieces of the old Link interface survive additional
finite permutation tests, provided the earlier actions are compatible. -/
noncomputable def link (k : Proper S) :
    Link D (old k) (data D S old X τ hτ) where
  incl := inclusion D S old L A hA X τ hτ B hB k
  incl_edge := inclusion_edge D S old L A hA X τ hτ B hB k
  delete := deletion D S old X τ hτ k
  delete_edge e he := by
    have h := deletion_edge D S old X τ hτ k e he
    by_cases hm : e ∈ k.val
    · simpa only [if_pos hm] using h
    · simpa only [if_neg hm] using h
  replace := inclusion_replace D S old L A hA X τ hτ B hB k

end AugmentedStep
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
