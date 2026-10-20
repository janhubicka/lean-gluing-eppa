import Mathlib

/-!
# Conjugating finite permutation coordinates

A bijection of the underlying finite quotient spaces induces a group
isomorphism of their symmetric groups. This explicit construction is used
when a graph automorphism reindexes the permutation coordinates in the
recursive Steiner valuation.
-/

namespace GluingEPPA.Steiner

universe u v
variable {X : Type u} {Y : Type v}

noncomputable def permutationConjugation (f : X ≃ Y) :
    Equiv.Perm X ≃* Equiv.Perm Y where
  toFun p := (f.symm.trans p).trans f
  invFun p := (f.trans p).trans f.symm
  left_inv p := by
    apply Equiv.ext
    intro x
    simp
  right_inv p := by
    apply Equiv.ext
    intro y
    simp
  map_mul' p q := by
    apply Equiv.ext
    intro y
    simp [Equiv.Perm.mul_apply]

theorem permutationConjugation_apply (f : X ≃ Y) (p : Equiv.Perm X) (x : X) :
    permutationConjugation f p (f x) = f (p x) := by
  simp [permutationConjugation]

theorem permutationConjugation_swap [DecidableEq X] [DecidableEq Y]
    (f : X ≃ Y) (x y : X) :
    permutationConjugation f (Equiv.swap x y) =
      Equiv.swap (f x) (f y) := by
  apply Equiv.ext
  intro z
  let x' := f.symm z
  have hz : z = f x' := (f.apply_symm_apply z).symm
  rw [hz]
  classical
  by_cases h : x' = x
  · subst x'
    simp [permutationConjugation, Equiv.swap_apply_def]
  · by_cases k : x' = y
    · subst x'
      simp [permutationConjugation, Equiv.swap_apply_def]
    · have hx : f x' ≠ f x := fun he => h (f.injective he)
      have hy : f x' ≠ f y := fun he => k (f.injective he)
      simp [permutationConjugation, Equiv.swap_apply_def, h, k, hx, hy]

end GluingEPPA.Steiner
