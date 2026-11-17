import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelTests
import GluingEPPA.Steiner.ChainValuation.AugmentedTestKernelTransport
import Mathlib.Algebra.Group.End

/-!
# Relabelling the real finite test-permutation coordinates

Conditional on old-stage RelabelData, the actual chain indices and
constructed chain-space equivalences yield injective homomorphisms of
opposite-permutation coordinates. This carries the entire added finite-test
word kernel, not just individual generator actions.
No actual recursive family naturality is assumed by these statements.
-/
namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData

universe u
variable {V E V' E' : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (D' : EdgeGraph V' E') [Finite V'] [Fintype E'] [DecidableEq E']
variable (S : Finset E) (T : Finset E')
variable (old : ∀ i : Proper S, Data E i.val)
variable (old' : ∀ i : Proper T, Data E' i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))
variable (L' : ∀ m t : Proper T, m.val ⊆ t.val → Link D' (old' m) (old' t))
variable {p : E ≃ E'}

/-- Conjugation, respecting the opposite multiplication convention of the
augmented record. -/
noncomputable def oppositePermHom {X Y : Type u} (F : X ≃ Y) :
    (Equiv.Perm X)ᵐᵒᵖ →* (Equiv.Perm Y)ᵐᵒᵖ where
  toFun a := MulOpposite.op (F.permCongrHom (MulOpposite.unop a))
  map_one' := by
    apply MulOpposite.unop_injective
    change F.permCongrHom 1 = 1
    exact map_one F.permCongrHom
  map_mul' := by
    intro a b
    apply MulOpposite.unop_injective
    change F.permCongrHom (MulOpposite.unop b * MulOpposite.unop a) =
      F.permCongrHom (MulOpposite.unop b) * F.permCongrHom (MulOpposite.unop a)
    exact map_mul F.permCongrHom _ _

theorem oppositePermHom_injective {X Y : Type u} (F : X ≃ Y) :
    Function.Injective (oppositePermHom F) := by
  intro a b hab
  apply MulOpposite.unop_injective
  apply F.permCongrHom.injective
  exact congrArg MulOpposite.unop hab

/-- Chosen equivalence of the genuine indexed test from the checked
matching-preserving existential theorem. -/
noncomputable def indexedSpaceEquiv
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) (c : SeparatedChains D N S old L) :
    chainSpace D N S old L c ≃
      chainSpace D' N T old' L'
        (chainIndexEquiv D D' S T old old' L L' R N c) :=
  Classical.choose (chainPerm_equivariant D D' S T old old' L L' R N c)

theorem indexedSpaceEquiv_perm
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) (c : SeparatedChains D N S old L) (e : E)
    (x : chainSpace D N S old L c) :
    indexedSpaceEquiv D D' S T old old' L L' R N c
        (chainPerm D N S old L c e x) =
      chainPerm D' N T old' L'
        (chainIndexEquiv D D' S T old old' L L' R N c)
        (p e) (indexedSpaceEquiv D D' S T old old' L L' R N c x) :=
  Classical.choose_spec (chainPerm_equivariant D D' S T old old' L L' R N c) e x

/-- Exact finite-test coordinate transport in the required opposite group. -/
theorem concreteTestCoordinates
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) :
    ∃ q : SeparatedChains D N S old L ≃ SeparatedChains D' N T old' L',
    ∃ F : ∀ c : SeparatedChains D N S old L,
        (Equiv.Perm (chainSpace D N S old L c))ᵐᵒᵖ →*
          (Equiv.Perm (chainSpace D' N T old' L' (q c)))ᵐᵒᵖ,
      (∀ c e, F c (MulOpposite.op (chainPerm D N S old L c e)) =
        MulOpposite.op (chainPerm D' N T old' L' (q c) (p e))) ∧
      (∀ c, Function.Injective (F c)) := by
  let q := chainIndexEquiv D D' S T old old' L L' R N
  let X := fun c => indexedSpaceEquiv D D' S T old old' L L' R N c
  let F := fun c => oppositePermHom (X c)
  refine ⟨q, F, ?_, ?_⟩
  · intro c e
    apply MulOpposite.unop_injective
    change (X c).permCongrHom (chainPerm D N S old L c e) =
      chainPerm D' N T old' L' (q c) (p e)
    ext y
    obtain ⟨x, rfl⟩ := (X c).surjective y
    simpa only [Equiv.permCongrHom_coe, Equiv.permCongr_apply,
      Equiv.symm_apply_apply] using
      (indexedSpaceEquiv_perm D D' S T old old' L L' R N c e x)
  · intro c
    exact oppositePermHom_injective (X c)

/-- Equality of all real chain-test word coordinates is invariant under
relabeling. This discharges the additional-test part of the augmented
word-kernel naturality induction, conditional on earlier-stage RelabelData. -/
theorem concreteTestKernel_iff
    (R : RelabelData D D' S T old old' L L' p) (N : Nat)
    (w v : List E) :
    GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.testValue
        (chainSpace D N S old L) (chainPerm D N S old L) w =
      GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.testValue
        (chainSpace D N S old L) (chainPerm D N S old L) v ↔
    GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.testValue
        (chainSpace D' N T old' L') (chainPerm D' N T old' L') (w.map p) =
      GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.testValue
        (chainSpace D' N T old' L') (chainPerm D' N T old' L') (v.map p) := by
  obtain ⟨q, F, hF, hinj⟩ := concreteTestCoordinates D D' S T old old' L L' R N
  exact GluingEPPA.Steiner.EdgeGraph.AugmentedRecord.testValue_kernel_iff
    p q (chainPerm D N S old L) (chainPerm D' N T old' L')
    F hF hinj w v

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
