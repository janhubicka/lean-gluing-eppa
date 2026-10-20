import Mathlib

/-!
# Reindexing a dependent product of groups

A bijection of index sets, together with a group isomorphism on every
corresponding coordinate, induces a group isomorphism of the dependent
products. This will permute the proper-subset coordinates in the
recursive finite group construction.
-/

namespace GluingEPPA.Steiner

universe u v w z
variable {I : Type u} {J : Type v}
variable (A : I → Type w) (B : J → Type z)
variable [∀ i, Group (A i)] [∀ j, Group (B j)]

noncomputable def reindexMap (p : I ≃ J)
    (f : ∀ i, A i ≃* B (p i))
    (x : ∀ i, A i) (j : J) : B j :=
  (p.apply_symm_apply j) ▸ f (p.symm j) (x (p.symm j))

theorem reindexMap_apply (p : I ≃ J)
    (f : ∀ i, A i ≃* B (p i))
    (x : ∀ i, A i) (i : I) :
    reindexMap A B p f x (p i) = f i (x i) := by
  unfold reindexMap
  have hi := p.symm_apply_apply i
  cases hi
  simp

noncomputable def reindexGroupEquiv (p : I ≃ J)
    (f : ∀ i, A i ≃* B (p i)) :
    (∀ i, A i) ≃* (∀ j, B j) where
  toFun := reindexMap A B p f
  invFun y i := (f i).symm (y (p i))
  left_inv x := by
    funext i
    change (f i).symm (reindexMap A B p f x (p i)) = x i
    simp [reindexMap_apply]
  right_inv y := by
    funext j
    obtain ⟨i,rfl⟩ := p.surjective j
    change reindexMap A B p f (fun i => (f i).symm (y (p i))) (p i) = y (p i)
    simp [reindexMap_apply]
  map_mul' x y := by
    funext j
    obtain ⟨i,rfl⟩ := p.surjective j
    change reindexMap A B p f (x * y) (p i) =
      reindexMap A B p f x (p i) * reindexMap A B p f y (p i)
    simp [reindexMap_apply, map_mul]

theorem reindexGroupEquiv_apply (p : I ≃ J)
    (f : ∀ i, A i ≃* B (p i))
    (x : ∀ i, A i) (i : I) :
    reindexGroupEquiv A B p f x (p i) = f i (x i) :=
  reindexMap_apply A B p f x i

end GluingEPPA.Steiner
