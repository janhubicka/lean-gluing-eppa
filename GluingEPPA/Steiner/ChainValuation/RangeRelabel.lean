import GluingEPPA.Steiner.ChainValuation.CosetRelabel

/-!
# Interface ranges and exact separation under relabelling

For each chain attachment the source and target intersection groups are
related by a multiplicative equivalence. If the square with the inclusion
homomorphisms commutes, the target image subgroup is precisely the image
of the source subgroup. In particular both cosets used by the separated
triple condition have the same intersection-emptiness truth value.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w z w2 z2
variable {G : Type u} {H : Type v} {K : Type w} {L : Type z}
variable {K2 : Type w2} {L2 : Type z2}
variable [Group G] [Group H] [Group K] [Group L]
variable [Group K2] [Group L2]

/-- Equality of the square of inclusion maps is enough to transport the
image subgroup exactly. No finiteness and no assumed injectivity. -/
theorem mem_range_relabel_iff
    (F : G ≃* H) (Q : K ≃* L)
    (i : K →* G) (j : L →* H)
    (h : ∀ k, F (i k) = j (Q k)) (g : G) :
    g ∈ i.range ↔ F g ∈ j.range := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Q k, (h k).symm⟩
  · rintro ⟨l, hl⟩
    obtain ⟨k, rfl⟩ := Q.surjective l
    refine ⟨k, ?_⟩
    exact F.injective ((h k).trans hl)

/-- A pair of matching subgroup-interface squares transports the entire
separation condition of one consecutive triple of chain blocks. -/
theorem disjoint_interface_cosets_relabel_iff
    (F : G ≃* H)
    (Q : K ≃* L) (Q' : K2 ≃* L2)
    (i : K →* G) (j : K2 →* G)
    (i' : L →* H) (j' : L2 →* H)
    (hi : ∀ k, F (i k) = i' (Q k))
    (hj : ∀ k, F (j k) = j' (Q' k))
    (g : G) :
    Disjoint (leftCoset i.range 1) (leftCoset j.range g) ↔
      Disjoint (leftCoset i'.range 1) (leftCoset j'.range (F g)) := by
  simpa only [map_one] using
    leftCoset_relabel_disjoint_iff F i.range j.range i'.range j'.range
      (fun x => mem_range_relabel_iff F Q i i' hi x)
      (fun x => mem_range_relabel_iff F Q' j j' hj x) 1 g

end GluingEPPA.Steiner.ChainValuation
