import Mathlib

/-!
# Coset identities used by the parameter-dependent chain construction

These are the algebraic inputs to chain restriction, not a proof of the
chain restriction theorem or existence of the new recursive valuation.
All groups are arbitrary; no commutativity, finiteness, or acyclicity is assumed.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {G : Type u} [Group G]

/-- The left coset `g H`, expressed by its membership criterion. -/
def leftCoset (H : Subgroup G) (g : G) : Set G :=
  {x | g⁻¹ * x ∈ H}

@[simp] theorem self_mem_leftCoset (H : Subgroup G) (g : G) :
    g ∈ leftCoset H g := by
  simp [leftCoset]

/-- Recentring a coset at any one of its points. -/
theorem leftCoset_eq_of_mem {H : Subgroup G} {g x : G}
    (hx : x ∈ leftCoset H g) : leftCoset H g = leftCoset H x := by
  change g⁻¹ * x ∈ H at hx
  ext y
  constructor
  · intro hy
    change g⁻¹ * y ∈ H at hy
    change x⁻¹ * y ∈ H
    have hm := H.mul_mem (H.inv_mem hx) hy
    convert hm using 1 <;> group
  · intro hy
    change x⁻¹ * y ∈ H at hy
    change g⁻¹ * y ∈ H
    have hm := H.mul_mem hx hy
    convert hm using 1 <;> group

/-- A nonempty intersection is the full coset of the intersection subgroup. -/
theorem leftCoset_inter_of_mem {H K : Subgroup G} {g h x : G}
    (hx : x ∈ leftCoset H g) (hy : x ∈ leftCoset K h) :
    leftCoset H g ∩ leftCoset K h = leftCoset (H ⊓ K) x := by
  rw [leftCoset_eq_of_mem hx, leftCoset_eq_of_mem hy]
  ext y
  rfl

/-- The exact subgroup identity needed when restricting one chain attachment. -/
theorem mask_coset_inter {E : Type v} (K : Set E → Subgroup G)
    (hcap : ∀ A B, K (A ∩ B) = K A ⊓ K B)
    {A B : Set E} {g h x : G}
    (hx : x ∈ leftCoset (K A) g) (hy : x ∈ leftCoset (K B) h) :
    leftCoset (K A) g ∩ leftCoset (K B) h = leftCoset (K (A ∩ B)) x := by
  rw [hcap]
  exact leftCoset_inter_of_mem hx hy

/-- The inverse/order calculation in the actual lifted intersection witness. -/
theorem reflection_coordinate {h a b q : G} (hab : a = h * b) :
    h * (q⁻¹ * b⁻¹)⁻¹ = a * q := by
  rw [hab]
  group

end GluingEPPA.Steiner.ChainValuation
