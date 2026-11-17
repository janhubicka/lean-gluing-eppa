import GluingEPPA.Steiner.ChainValuation.AugmentedTestKernelTransport
import Mathlib.Algebra.Group.End

/-!
# Conjugating the augmented record's finite permutation coordinates

A bijection of finite test spaces conjugating every named letter induces
an injective homomorphism of their *opposite* permutation groups. Thus the
finite-test part of augmented naturality needs only a pointwise bijection
of the actual chain spaces and letter equivariance, not an extra
group-homomorphism assumption.
-/

namespace GluingEPPA.Steiner.EdgeGraph.AugmentedRecord

universe u
variable {X Y : Type u}

/-- Conjugation by a test-space equivalence is a homomorphism on the
opposite permutation groups used by the valuation record. -/
noncomputable def testCoordinateConj (F : X ≃ Y) :
    (Equiv.Perm X)ᵐᵒᵖ →* (Equiv.Perm Y)ᵐᵒᵖ where
  toFun s := MulOpposite.op (F.permCongrHom (MulOpposite.unop s))
  map_one' := by
    apply MulOpposite.unop_injective
    change F.permCongrHom 1 = 1
    exact map_one _
  map_mul' s t := by
    apply MulOpposite.unop_injective
    change F.permCongrHom (MulOpposite.unop t * MulOpposite.unop s) =
      F.permCongrHom (MulOpposite.unop t) *
        F.permCongrHom (MulOpposite.unop s)
    exact map_mul _ _ _

theorem testCoordinateConj_injective (F : X ≃ Y) :
    Function.Injective (testCoordinateConj F) := by
  intro s t h
  apply MulOpposite.unop_injective
  apply (F.permCongrHom).injective
  exact congrArg MulOpposite.unop h

/-- Pointwise intertwining of the named permutations is precisely
the generator equation needed by augmented test-record naturality. -/
theorem testCoordinateConj_letter {E E' : Type u}
    (p : E ≃ E') (F : X ≃ Y)
    (τ : E → Equiv.Perm X) (τ' : E' → Equiv.Perm Y)
    (hF : ∀ e x, F (τ e x) = τ' (p e) (F x))
    (e : E) :
    testCoordinateConj F (MulOpposite.op (τ e)) =
      MulOpposite.op (τ' (p e)) := by
  apply MulOpposite.unop_injective
  change F.permCongrHom (τ e) = τ' (p e)
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := F.surjective y
  simpa [Equiv.permCongrHom_coe, Equiv.permCongr_apply] using hF e x

/-- Equality of entire finite-test word records is equivalent under
a bijective reindexing of tests with equivariant space bijections.
There is no separate permutation-homomorphism assumption. -/
theorem testValue_kernel_iff_of_equivariant
    {E E' J J' : Type u}
    {X : J → Type u} {X' : J' → Type u}
    (p : E ≃ E') (q : J ≃ J')
    (τ : ∀ j : J, E → Equiv.Perm (X j))
    (τ' : ∀ j' : J', E' → Equiv.Perm (X' j'))
    (F : ∀ j : J, X j ≃ X' (q j))
    (hF : ∀ j e x, F j (τ j e x) =
      τ' (q j) (p e) (F j x))
    (w v : List E) :
    testValue X τ w = testValue X τ v ↔
      testValue X' τ' (w.map p) = testValue X' τ' (v.map p) :=
  testValue_kernel_iff p q τ τ'
    (fun j => testCoordinateConj (F j))
    (fun j e => testCoordinateConj_letter p (F j) (τ j)
      (τ' (q j)) (hF j) e)
    (fun j => testCoordinateConj_injective (F j))
    w v

end GluingEPPA.Steiner.EdgeGraph.AugmentedRecord
