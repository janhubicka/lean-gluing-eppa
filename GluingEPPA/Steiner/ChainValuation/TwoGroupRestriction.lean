import GluingEPPA.Steiner.ChainValuation.MatchingComponents

/-!
# Restricted attachment matching across two different Cayley groups

The adjacent blocks K_A and K_B of a chain are different groups. They
are glued along embeddings of the previously constructed common group
K_(A∩B). An M-piece meets this attachment along the pullback of its
restricted subgroup. The two pullbacks must agree.

This two-group formulation, unlike a same-ambient-group coset lemma,
matches the actual well-founded construction and needs no embedding
of the not-yet-constructed K_S.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {H : Type u} {G : Type v} {K : Type w}
variable [Group H] [Group G] [Group K]

/-- A restricted piece of the old G block and one of the new K block
have a common attachment point indexed by k in the earlier group H. -/
def TwoGroupAttachment
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K) (h : G)
    (oldPiece : Set G) (newPiece : Set K) : Prop :=
  ∃ k : H, oldPiece = leftCoset P (h * i k) ∧
    newPiece = leftCoset Q (j k)

/-- If two attachment points lie in one new restricted piece, their old
restricted cosets coincide. The common pullback is the triple mask subgroup.
No commutativity or ambient full-stage group is needed. -/
theorem twoGroupAttachment_old_unique
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K)
    (hcomap : P.comap i = Q.comap j) (h : G)
    {old₁ old₂ : Set G} {newPiece : Set K}
    (h₁ : TwoGroupAttachment i j P Q h old₁ newPiece)
    (h₂ : TwoGroupAttachment i j P Q h old₂ newPiece) :
    old₁ = old₂ := by
  obtain ⟨k₁, hold₁, hnew₁⟩ := h₁
  obtain ⟨k₂, hold₂, hnew₂⟩ := h₂
  have hcoset : leftCoset Q (j k₁) = leftCoset Q (j k₂) :=
    hnew₁.symm.trans hnew₂
  have hmem : j k₂ ∈ leftCoset Q (j k₁) := by
    rw [hcoset]
    exact self_mem_leftCoset Q (j k₂)
  have hQ : (j k₁)⁻¹ * j k₂ ∈ Q := hmem
  have hpull : k₁⁻¹ * k₂ ∈ Q.comap j := by
    change j (k₁⁻¹ * k₂) ∈ Q
    simpa only [map_mul, map_inv] using hQ
  have hPpull : k₁⁻¹ * k₂ ∈ P.comap i := by
    rw [hcomap]
    exact hpull
  have hP : (i k₁)⁻¹ * i k₂ ∈ P := by
    change i (k₁⁻¹ * k₂) ∈ P at hPpull
    simpa only [map_mul, map_inv] using hPpull
  have hOld : leftCoset P (h * i k₁) = leftCoset P (h * i k₂) := by
    apply leftCoset_eq_of_mem
    change (h * i k₁)⁻¹ * (h * i k₂) ∈ P
    convert hP using 1 <;> group
  rw [hold₁, hold₂]
  exact hOld

/-- Conversely, an old restricted piece attaches to at most one new piece. -/
theorem twoGroupAttachment_new_unique
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K)
    (hcomap : P.comap i = Q.comap j) (h : G)
    {oldPiece : Set G} {new₁ new₂ : Set K}
    (h₁ : TwoGroupAttachment i j P Q h oldPiece new₁)
    (h₂ : TwoGroupAttachment i j P Q h oldPiece new₂) :
    new₁ = new₂ := by
  obtain ⟨k₁, hold₁, hnew₁⟩ := h₁
  obtain ⟨k₂, hold₂, hnew₂⟩ := h₂
  have hcoset : leftCoset P (h * i k₁) = leftCoset P (h * i k₂) :=
    hold₁.symm.trans hold₂
  have hmem : h * i k₂ ∈ leftCoset P (h * i k₁) := by
    rw [hcoset]
    exact self_mem_leftCoset P (h * i k₂)
  have hP : (i k₁)⁻¹ * i k₂ ∈ P := by
    change (h * i k₁)⁻¹ * (h * i k₂) ∈ P at hmem
    convert hmem using 1 <;> group
  have hpull : k₁⁻¹ * k₂ ∈ P.comap i := by
    change i (k₁⁻¹ * k₂) ∈ P
    simpa only [map_mul, map_inv] using hP
  have hQpull : k₁⁻¹ * k₂ ∈ Q.comap j := by
    rw [← hcomap]
    exact hpull
  have hQ : (j k₁)⁻¹ * j k₂ ∈ Q := by
    change j (k₁⁻¹ * k₂) ∈ Q at hQpull
    simpa only [map_mul, map_inv] using hQpull
  have hNew : leftCoset Q (j k₁) = leftCoset Q (j k₂) :=
    leftCoset_eq_of_mem hQ
  rw [hnew₁, hnew₂]
  exact hNew

/-- Thus the connections between restricted coset pieces across a chain
attachment form a genuine bipartite matching. -/
def twoGroupAttachmentMatching
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K)
    (hcomap : P.comap i = Q.comap j) (h : G) :
    Matching (Sum (Set G) (Set K)) where
  Rel x y :=
    match x, y with
    | .inl oldPiece, .inr newPiece =>
        TwoGroupAttachment i j P Q h oldPiece newPiece
    | .inr newPiece, .inl oldPiece =>
        TwoGroupAttachment i j P Q h oldPiece newPiece
    | _, _ => False
  symm := by
    intro x y hxy
    cases x <;> cases y <;> exact hxy
  unique := by
    intro x y z hxy hxz
    cases x with
    | inl oldPiece =>
      cases y with
      | inl _ => cases hxy
      | inr a =>
        cases z with
        | inl _ => cases hxz
        | inr _ =>
          congr 1
          exact twoGroupAttachment_new_unique i j P Q hcomap h hxy hxz
    | inr newPiece =>
      cases y with
      | inr _ => cases hxy
      | inl _ =>
        cases z with
        | inr _ => cases hxz
        | inl _ =>
          congr 1
          exact twoGroupAttachment_old_unique i j P Q hcomap h hxy hxz

/-- Distinct old restricted cosets cannot merge through the new block. -/
theorem twoGroup_old_components_injective
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K)
    (hcomap : P.comap i = Q.comap j) (h : G) :
    Function.Injective
      (fun oldPiece : Set G =>
        Quotient.mk (twoGroupAttachmentMatching i j P Q hcomap h).componentSetoid
          (Sum.inl oldPiece)) := by
  apply Matching.inl_component_injective
  intro x x' hx
  exact hx

/-- Distinct new restricted cosets also remain distinct. -/
theorem twoGroup_new_components_injective
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K)
    (hcomap : P.comap i = Q.comap j) (h : G) :
    Function.Injective
      (fun newPiece : Set K =>
        Quotient.mk (twoGroupAttachmentMatching i j P Q hcomap h).componentSetoid
          (Sum.inr newPiece)) := by
  apply Matching.inr_component_injective
  intro x x' hx
  exact hx

end GluingEPPA.Steiner.ChainValuation
