import GluingEPPA.Steiner.ChainValuation.TwoGroupRestriction

/-!
# Pullbacks of exact subgroup intersections

Adjacent chain blocks live in different earlier groups. A commuting square,
injectivity of the common attaching group, and exact subgroup intersection
in each block imply equality of the pulled-back restricted subgroups.
This is the missing hypothesis of the two-group restricted-piece matching.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w z r s
variable {H : Type u} {G : Type v} {K : Type w} {C : Type z}
variable {P : Type r} {Q : Type s}
variable [Group H] [Group G] [Group K] [Group C]
variable [Group P] [Group Q]

/-- In a commuting square with exact image intersection, the pullback of
the second image is exactly the common smaller subgroup. -/
theorem comap_range_of_exact_intersection
    (i : H →* G) (j : K →* G) (a : C →* H) (b : C →* K)
    (hi : Function.Injective i)
    (hcomm : i.comp a = j.comp b)
    (hinter : i.range ⊓ j.range = (i.comp a).range) :
    j.range.comap i = a.range := by
  ext x
  constructor
  · intro hx
    have hboth : i x ∈ i.range ⊓ j.range := ⟨⟨x, rfl⟩, hx⟩
    rw [hinter] at hboth
    obtain ⟨c, hc⟩ := hboth
    have heq : i (a c) = i x := by
      simpa only [MonoidHom.comp_apply] using hc
    exact ⟨c, hi heq⟩
  · rintro ⟨c, rfl⟩
    change i (a c) ∈ j.range
    refine ⟨b c, ?_⟩
    have hc := DFunLike.congr_fun hcomm c
    change i (a c) = j (b c) at hc
    exact hc.symm

/-- The two ambient blocks have the same restricted subgroup on their
common attaching group, whenever both intersection squares are exact. -/
theorem two_block_pullbacks_agree
    (i : H →* G) (j : H →* K)
    (p : P →* G) (q : Q →* K)
    (a : C →* H) (b : C →* P) (c : C →* Q)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hcommG : i.comp a = p.comp b)
    (hcommK : j.comp a = q.comp c)
    (hinterG : i.range ⊓ p.range = (i.comp a).range)
    (hinterK : j.range ⊓ q.range = (j.comp a).range) :
    p.range.comap i = q.range.comap j := by
  calc
    p.range.comap i = a.range :=
      comap_range_of_exact_intersection i p a b hi hcommG hinterG
    _ = q.range.comap j :=
      (comap_range_of_exact_intersection j q a c hj hcommK hinterK).symm

end GluingEPPA.Steiner.ChainValuation
