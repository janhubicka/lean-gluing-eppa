import GluingEPPA.Steiner.ChainValuation.PushoutEquiv
import GluingEPPA.Steiner.ChainValuation.TwoGroupRestriction

/-!
# Normalization of noncommutative restricted Cayley cosets

A historical M-component intersects a block K_A in a single translated
left coset of the actual earlier subgroup K_(M∩A). The chart from the
earlier group to this coset is bijective, not merely a surjection. It
intertwines every named right multiplication by an earlier generator.

At an attachment, the points of a restricted coset on the interface
are exactly the elements of a coset of the pulled-back subgroup.
The equality of these pullback subgroups gives a common interface
chart for both sides of the attachment.

The next induction must glue these charts into the normalized
smaller-mask separated-chain test and prove edge reflection there.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {H : Type u} {G : Type v} {K : Type w}
variable [Group H] [Group G] [Group K]

/-- A translated copy of an included earlier group is exactly the
corresponding left coset, with no unintended identifications. -/
noncomputable def leftCosetChart
    (i : H →* G) (hi : Function.Injective i) (g : G) :
    H ≃ {x : G // x ∈ leftCoset i.range g} := by
  let f : H → {x : G // x ∈ leftCoset i.range g} :=
    fun h => ⟨g * i h, by
      change g⁻¹ * (g * i h) ∈ i.range
      have hh : g⁻¹ * (g * i h) = i h := by group
      rw [hh]
      exact ⟨h, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    apply hi
    apply mul_left_cancel (congrArg Subtype.val hxy)
  · intro ⟨x, hx⟩
    change g⁻¹ * x ∈ i.range at hx
    obtain ⟨z, hz⟩ := hx
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change g * i z = x
    rw [hz]
    group

/-- The chart really is left translation of the earlier inclusion. -/
@[simp] theorem leftCosetChart_val
    (i : H →* G) (hi : Function.Injective i) (g : G) (x : H) :
    ((leftCosetChart i hi g) x).val = g * i x := rfl

/-- Right multiplication inside a normalized earlier coset is carried
to right multiplication by its image, without assuming commutativity. -/
theorem leftCosetChart_right_mul
    (i : H →* G) (hi : Function.Injective i)
    (g : G) (x y : H) :
    ((leftCosetChart i hi g) (x * y)).val =
      ((leftCosetChart i hi g) x).val * i y := by
  simp only [leftCosetChart_val, map_mul, mul_assoc]

/-- The subset of a common attaching subgroup that lies inside a
restricted old-side coset is precisely a coset of the pulled-back
restricted subgroup. This is a pointwise, iff-level statement. -/
theorem restrictedAttachment_fibre_iff
    (i : H →* G) (P : Subgroup G) (g : G) (k t : H) :
    g * i t ∈ leftCoset P (g * i k) ↔
      t ∈ leftCoset (P.comap i) k := by
  change (g * i k)⁻¹ * (g * i t) ∈ P ↔
    k⁻¹ * t ∈ P.comap i
  have heq : (g * i k)⁻¹ * (g * i t) = i (k⁻¹ * t) := by
    simp only [map_mul, map_inv]
    group
  rw [heq]
  rfl

/-- The two sides of a group attachment select *exactly the same*
parameters for the restricted interface whenever their subgroup
pullbacks agree. -/
theorem restrictedAttachment_fibres_agree
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K)
    (hcomap : P.comap i = Q.comap j)
    (g : G) (k t : H) :
    g * i t ∈ leftCoset P (g * i k) ↔
      j t ∈ leftCoset Q (j k) := by
  rw [restrictedAttachment_fibre_iff
    i P g k t]
  have hr : j t ∈ leftCoset Q (j k) ↔
      t ∈ leftCoset (Q.comap j) k := by
    simpa only [one_mul] using
      (restrictedAttachment_fibre_iff j Q (1 : K) k t)
  rw [hr]
  rw [hcomap]

end GluingEPPA.Steiner.ChainValuation
