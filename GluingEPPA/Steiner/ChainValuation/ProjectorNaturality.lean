import GluingEPPA.Steiner.ChainValuation.LinkProjectors

/-!
# Naturality of earlier-mask deletion/inclusion projectors

One can pull back an allowed-mask subgroup along an earlier inclusion by
intersecting the masks. This is proved directly from generator rules for
the Link maps, without an ambient full-stage valuation group.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

/-- Taking the M-projector commutes with inclusion from I after restricting
M to M∩I. -/
theorem projector_natural (m i t : Proper S)
    (hmt : m.val ⊆ t.val) (hit : i.val ⊆ t.val) :
    (projector D S old L m t hmt).comp (L i t hit).incl =
      (L i t hit).incl.comp
        (projector D S old L (Step.meet S m i) i
          Finset.inter_subset_right) := by
  apply (old i).hom_ext
  intro e he
  change projector D S old L m t hmt
      ((L i t hit).incl ((old i).edge e)) =
    (L i t hit).incl
      (projector D S old L (Step.meet S m i) i
        Finset.inter_subset_right ((old i).edge e))
  rw [(L i t hit).incl_edge e he,
    projector_edge D S old L m t hmt e (hit he),
    projector_edge D S old L (Step.meet S m i) i
      Finset.inter_subset_right e he]
  by_cases hm : e ∈ m.val
  · have hmi : e ∈ (Step.meet S m i).val :=
      Finset.mem_inter.mpr ⟨hm, he⟩
    simp only [if_pos hm, if_pos hmi,
      (L i t hit).incl_edge e he]
  · have hmi : e ∉ (Step.meet S m i).val := by
      intro h
      exact hm (Finset.mem_inter.mp h).1
    simp only [if_neg hm, if_neg hmi, map_one]

/-- Pullback of an earlier image subgroup is the intersection-mask subgroup
in the smaller stage. -/
theorem comap_range (m i t : Proper S)
    (hmt : m.val ⊆ t.val) (hit : i.val ⊆ t.val) :
    (L m t hmt).incl.range.comap (L i t hit).incl =
      (L (Step.meet S m i) i Finset.inter_subset_right).incl.range := by
  ext g
  have hnat := DFunLike.congr_fun
    (projector_natural D S old L m i t hmt hit) g
  change projector D S old L m t hmt ((L i t hit).incl g) =
    (L i t hit).incl
      (projector D S old L (Step.meet S m i) i
        Finset.inter_subset_right g) at hnat
  constructor
  · intro hm
    have hfix := (mem_range_iff_projector D S old L m t hmt
      ((L i t hit).incl g)).mp hm
    rw [hnat] at hfix
    have hi : Function.Injective (L i t hit).incl :=
      Link.injective D (old i) (old t) hit (L i t hit)
    have hg := hi hfix
    exact (mem_range_iff_projector D S old L
      (Step.meet S m i) i Finset.inter_subset_right g).mpr hg
  · intro hm
    have hg := (mem_range_iff_projector D S old L
      (Step.meet S m i) i Finset.inter_subset_right g).mp hm
    have hfix : projector D S old L m t hmt
        ((L i t hit).incl g) = (L i t hit).incl g := by
      rw [hnat, hg]
    exact (mem_range_iff_projector D S old L m t hmt
      ((L i t hit).incl g)).mpr hfix

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
