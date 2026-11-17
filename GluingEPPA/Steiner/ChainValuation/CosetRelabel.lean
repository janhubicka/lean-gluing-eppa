import GluingEPPA.Steiner.ChainValuation.Cosets

/-!
# Relabelling the separation condition on chain attachments

Separation in the bounded-chain tests is emptiness of an intersection of two
cosets in a single earlier group. A multiplicative equivalence transporting
each of the two interface subgroups preserves that condition *in both
directions*. This is the group-theoretic portion of augmented naturality;
actual diagram relabelling must still supply compatible group equivalences.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- A group equivalence carrying a subgroup onto another preserves and
reflects membership in each of its left cosets. -/
theorem leftCoset_relabel_mem_iff (F : G ≃* H)
    (K : Subgroup G) (K' : Subgroup H)
    (hK : ∀ x : G, x ∈ K ↔ F x ∈ K')
    (g x : G) :
    x ∈ leftCoset K g ↔ F x ∈ leftCoset K' (F g) := by
  change g⁻¹ * x ∈ K ↔ (F g)⁻¹ * F x ∈ K'
  simpa only [map_mul, map_inv] using hK (g⁻¹ * x)

/-- Exact disjointness of two attaching cosets is invariant under any
compatible equivalence of their old-group coordinates. No commutativity,
finiteness, or chain-normalization argument is required. -/
theorem leftCoset_relabel_disjoint_iff (F : G ≃* H)
    (K L : Subgroup G) (K' L' : Subgroup H)
    (hK : ∀ x : G, x ∈ K ↔ F x ∈ K')
    (hL : ∀ x : G, x ∈ L ↔ F x ∈ L')
    (g h : G) :
    Disjoint (leftCoset K g) (leftCoset L h) ↔
      Disjoint (leftCoset K' (F g)) (leftCoset L' (F h)) := by
  constructor
  · intro hd
    apply Set.disjoint_left.mpr
    intro y hyK hyL
    obtain ⟨x, rfl⟩ := F.surjective y
    apply (Set.disjoint_left.mp hd)
      ((leftCoset_relabel_mem_iff F K K' hK g x).mpr hyK)
      ((leftCoset_relabel_mem_iff F L L' hL h x).mpr hyL)
  · intro hd
    apply Set.disjoint_left.mpr
    intro x hxK hxL
    apply (Set.disjoint_left.mp hd)
      ((leftCoset_relabel_mem_iff F K K' hK g x).mp hxK)
      ((leftCoset_relabel_mem_iff F L L' hL h x).mp hxL)

end GluingEPPA.Steiner.ChainValuation
