import GluingEPPA.Steiner.ChainValuation.ChainRestrictionCore
import GluingEPPA.Steiner.ChainValuation.Matching

/-!
# Restricting one Cayley-chain attachment gives a matching of cosets

The essential geometric consequence of the triple-intersection identity is
not merely that an attachment coset is connected: each restricted coset on
either side of an attachment meets at most one restricted coset on the
other side. This is the no-merging/no-splitting step in chain restriction.

No quotient, cardinality hypothesis, or commutativity is used.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u
variable {G : Type u} [Group G]

/-- The old P-piece and the new Q-piece meet at an attachment point h*k,
with k in the common attachment subgroup I. -/
def RestrictedAttachment (P Q I : Subgroup G) (h : G)
    (oldPiece newPiece : Set G) : Prop :=
  ∃ k : G, k ∈ I ∧
    oldPiece = leftCoset P (h * k) ∧ newPiece = leftCoset Q k

/-- One new restricted component attaches to at most one old one. -/
theorem restrictedAttachment_old_unique
    {P Q I R : Subgroup G}
    (hPI : P ⊓ I = R) (hQI : Q ⊓ I = R)
    (h : G) {old₁ old₂ newPiece : Set G}
    (h₁ : RestrictedAttachment P Q I h old₁ newPiece)
    (h₂ : RestrictedAttachment P Q I h old₂ newPiece) :
    old₁ = old₂ := by
  obtain ⟨k₁, hk₁, hold₁, hnew₁⟩ := h₁
  obtain ⟨k₂, hk₂, hold₂, hnew₂⟩ := h₂
  have hsame : leftCoset Q k₁ = leftCoset Q k₂ :=
    hnew₁.symm.trans hnew₂
  rw [hold₁, hold₂]
  exact attachment_no_merge hPI hQI hk₁ hk₂ hsame

/-- One old restricted component attaches to at most one new one. -/
theorem restrictedAttachment_new_unique
    {P Q I R : Subgroup G}
    (hPI : P ⊓ I = R) (hQI : Q ⊓ I = R)
    (h : G) {oldPiece new₁ new₂ : Set G}
    (h₁ : RestrictedAttachment P Q I h oldPiece new₁)
    (h₂ : RestrictedAttachment P Q I h oldPiece new₂) :
    new₁ = new₂ := by
  obtain ⟨k₁, hk₁, hold₁, hnew₁⟩ := h₁
  obtain ⟨k₂, hk₂, hold₂, hnew₂⟩ := h₂
  have hold : leftCoset P (h * k₁) = leftCoset P (h * k₂) :=
    hold₁.symm.trans hold₂
  have hmem : h * k₂ ∈ leftCoset P (h * k₁) := by
    rw [hold]
    exact self_mem_leftCoset P (h * k₂)
  have hP : k₁⁻¹ * k₂ ∈ P := by
    change (h * k₁)⁻¹ * (h * k₂) ∈ P at hmem
    convert hmem using 1 <;> group
  have hI : k₁⁻¹ * k₂ ∈ I := I.mul_mem (I.inv_mem hk₁) hk₂
  have hR : k₁⁻¹ * k₂ ∈ R := by
    rw [← hPI]
    exact ⟨hP, hI⟩
  have hQ : k₁⁻¹ * k₂ ∈ Q := by
    rw [← hQI] at hR
    exact hR.1
  have hcoset : leftCoset Q k₁ = leftCoset Q k₂ :=
    leftCoset_eq_of_mem hQ
  rw [hnew₁, hnew₂]
  exact hcoset

/-- A restricted attachment is literally a partial matching between the
coset pieces of its two adjacent blocks. -/
def restrictedAttachmentMatching
    {P Q I R : Subgroup G}
    (hPI : P ⊓ I = R) (hQI : Q ⊓ I = R)
    (h : G) : Matching (Sum (Set G) (Set G)) where
  Rel x y :=
    match x, y with
    | .inl oldPiece, .inr newPiece =>
        RestrictedAttachment P Q I h oldPiece newPiece
    | .inr newPiece, .inl oldPiece =>
        RestrictedAttachment P Q I h oldPiece newPiece
    | _, _ => False
  symm := by
    intro x y hxy
    cases x <;> cases y <;> exact hxy
  unique := by
    intro x y z hxy hxz
    cases x with
    | inl oldPiece =>
      cases y with
      | inl a => cases hxy
      | inr a =>
        cases z with
        | inl b => cases hxz
        | inr b =>
          congr 1
          exact restrictedAttachment_new_unique hPI hQI h hxy hxz
    | inr newPiece =>
      cases y with
      | inr a => cases hxy
      | inl a =>
        cases z with
        | inr b => cases hxz
        | inl b =>
          congr 1
          exact restrictedAttachment_old_unique hPI hQI h hxy hxz

end GluingEPPA.Steiner.ChainValuation
