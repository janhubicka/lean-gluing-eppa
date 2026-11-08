import GluingEPPA.Steiner.ChainValuation.ChainRestrictionCore

/-!
# Mask-level attachment identities for chain restriction

These are the exact subgroup/coset calculations appearing when a chain block
with alphabet A is restricted to M and glued to a neighbouring block B.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {G : Type u} [Group G] {E : Type v}

/-- The intersection of one restricted block coset with an attachment coset
is exactly one coset of the triple-intersection subgroup. -/
theorem mask_attachment_piece
    (K : Set E → Subgroup G)
    (hcap : ∀ A B, K (A ∩ B) = K A ⊓ K B)
    {M A B : Set E} {p q x : G}
    (hx : x ∈ leftCoset (K (M ∩ A)) p)
    (hy : x ∈ leftCoset (K (A ∩ B)) q) :
    leftCoset (K (M ∩ A)) p ∩ leftCoset (K (A ∩ B)) q =
      leftCoset (K ((M ∩ A) ∩ (A ∩ B))) x :=
  mask_coset_inter K hcap hx hy

/-- The two triple intersections at an A--B attachment are the same subgroup. -/
theorem mask_triple_intersection
    (K : Set E → Subgroup G)
    (hcap : ∀ A B, K (A ∩ B) = K A ⊓ K B)
    (M A B : Set E) :
    K (M ∩ A) ⊓ K (A ∩ B) = K (M ∩ B) ⊓ K (A ∩ B) := by
  rw [← hcap, ← hcap]
  congr 1
  ext e
  simp only [Set.mem_inter_iff]
  aesop

/-- If two attachment pieces enter the same restricted component of the new
block, then the corresponding pieces came from the same restricted coset in
the old block. This is the no-merging step in the chain-restriction induction. -/
theorem mask_attachment_no_merge
    (K : Set E → Subgroup G)
    (hcap : ∀ A B, K (A ∩ B) = K A ⊓ K B)
    {M A B : Set E} {h k₁ k₂ : G}
    (hk₁ : k₁ ∈ K (A ∩ B)) (hk₂ : k₂ ∈ K (A ∩ B))
    (hsame : leftCoset (K (M ∩ B)) k₁ =
      leftCoset (K (M ∩ B)) k₂) :
    leftCoset (K (M ∩ A)) (h * k₁) =
      leftCoset (K (M ∩ A)) (h * k₂) := by
  apply attachment_no_merge
    (P := K (M ∩ A)) (Q := K (M ∩ B))
    (I := K (A ∩ B))
    (R := K (M ∩ A) ⊓ K (A ∩ B))
    rfl
  · exact (mask_triple_intersection K hcap M A B).symm
  · exact hk₁
  · exact hk₂
  · exact hsame

end GluingEPPA.Steiner.ChainValuation
