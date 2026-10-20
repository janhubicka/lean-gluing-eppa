import GluingEPPA.Steiner.ProductReindex
import GluingEPPA.Steiner.PermutationConjugation
import GluingEPPA.Steiner.RecursiveStep

/-!
# Isomorphisms of recursively indexed product coordinates

An isomorphism of each old group and each old transport quotient yields
an isomorphism of the corresponding old group/permutation coordinate.
Reindexing the coordinates gives the ambient isomorphism used in the
next recursive construction step.
-/

namespace GluingEPPA.Steiner.RecursiveStep

universe u v w z a b
variable {I : Type u} {J : Type v} {V : Type w} {W : Type z}
variable (A : I → Type a) (B : J → Type b)
variable [∀ i, Group (A i)] [∀ j, Group (B j)]
variable (T : ∀ i, Transport V (A i)) (U : ∀ j, Transport W (B j))

noncomputable def pairGroupIso {G H : Type*} [Group G] [Group H]
    {X Y : Type*} (f : G ≃* H) (q : X ≃ Y) :
    (G × Equiv.Perm X) ≃* (H × Equiv.Perm Y) where
  toFun x := (f x.1, permutationConjugation q x.2)
  invFun x := (f.symm x.1, (permutationConjugation q).symm x.2)
  left_inv x := by
    apply Prod.ext
    · exact f.symm_apply_apply x.1
    · exact (permutationConjugation q).symm_apply_apply x.2
  right_inv x := by
    apply Prod.ext
    · exact f.apply_symm_apply x.1
    · exact (permutationConjugation q).apply_symm_apply x.2
  map_mul' x y := by
    apply Prod.ext
    · change f (x.1 * y.1) = f x.1 * f y.1
      exact map_mul f x.1 y.1
    · change permutationConjugation q (x.2 * y.2) =
        permutationConjugation q x.2 * permutationConjugation q y.2
      exact map_mul (permutationConjugation q) x.2 y.2

noncomputable def productCoordinateIso
    (p : I ≃ J)
    (f : ∀ i, A i ≃* B (p i))
    (q : ∀ i, (T i).Space ≃ (U (p i)).Space) :
    Product A T ≃* Product B U :=
  reindexGroupEquiv
    (fun i => A i × Equiv.Perm (T i).Space)
    (fun j => B j × Equiv.Perm (U j).Space)
    p (fun i => pairGroupIso (f i) (q i))

end GluingEPPA.Steiner.RecursiveStep
