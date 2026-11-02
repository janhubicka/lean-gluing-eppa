import GluingEPPA.Steiner.ChainValuation.Cosets

/-!
# Algebraic core of chain restriction

This isolates the noncommutative step which prevents a restricted attachment
from merging two previously distinct restricted components. It is independent
of the finite quotient implementation of chains.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u
variable {G : Type u} [Group G]

/-- If two points of an attachment subgroup lie in the same new restricted
coset, then they differ by the triple-intersection subgroup. -/
theorem attachment_same_intersection_coset
    {Q I R : Subgroup G} (hQI : Q ⊓ I = R)
    {k₁ k₂ : G} (hk₁ : k₁ ∈ I) (hk₂ : k₂ ∈ I)
    (hsame : leftCoset Q k₁ = leftCoset Q k₂) :
    leftCoset R k₁ = leftCoset R k₂ := by
  have hk₂Q : k₂ ∈ leftCoset Q k₁ := by
    rw [hsame]
    exact self_mem_leftCoset Q k₂
  have hQ : k₁⁻¹ * k₂ ∈ Q := hk₂Q
  have hI : k₁⁻¹ * k₂ ∈ I := I.mul_mem (I.inv_mem hk₁) hk₂
  have hR : k₁⁻¹ * k₂ ∈ R := by
    rw [← hQI]
    exact ⟨hQ, hI⟩
  apply leftCoset_eq_of_mem
  exact hR

/-- The no-merging calculation at one chain attachment.

P is the old restricted subgroup, Q the new restricted subgroup, I
the attachment subgroup, and R their common triple intersection. If two
attachment pieces land in one Q-coset on the new side, then their translated
old endpoints already lie in one P-coset. -/
theorem attachment_no_merge
    {P Q I R : Subgroup G}
    (hPI : P ⊓ I = R) (hQI : Q ⊓ I = R)
    {h k₁ k₂ : G} (hk₁ : k₁ ∈ I) (hk₂ : k₂ ∈ I)
    (hsame : leftCoset Q k₁ = leftCoset Q k₂) :
    leftCoset P (h * k₁) = leftCoset P (h * k₂) := by
  have hRcoset :=
    attachment_same_intersection_coset hQI hk₁ hk₂ hsame
  have hk₂R : k₂ ∈ leftCoset R k₁ := by
    rw [hRcoset]
    exact self_mem_leftCoset R k₂
  have hR : k₁⁻¹ * k₂ ∈ R := hk₂R
  have hP : k₁⁻¹ * k₂ ∈ P := by
    rw [← hPI] at hR
    exact hR.1
  apply leftCoset_eq_of_mem
  change (h * k₁)⁻¹ * (h * k₂) ∈ P
  convert hP using 1 <;> group

/-- Restricting two disjoint attachment sets cannot make them intersect. -/
theorem restricted_attachments_disjoint
    {X : Type u} {A B A' B' : Set X}
    (hA : A' ⊆ A) (hB : B' ⊆ B) (h : Disjoint A B) :
    Disjoint A' B' :=
  h.mono hA hB

end GluingEPPA.Steiner.ChainValuation
