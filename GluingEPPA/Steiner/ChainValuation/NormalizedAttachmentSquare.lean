import GluingEPPA.Steiner.ChainValuation.LinkTripleInterface
import GluingEPPA.Steiner.ChainValuation.RestrictedCosetChart

/-!
# Noncommutative normalization of one matched coset attachment

At a genuine chain boundary, select coset representatives a in the
old block and j(k) in the new block. The old attachment point
h*i(k) belongs to a left coset of the earlier restricted subgroup.
There is a **unique** normalized shift u satisfying
a*p(u) = h*i(k), where p includes that restricted group.

For the triple-mask subgroup, commutative inclusion squares show
that the normalized attachment (u*s(w), t(w)) maps to the *exact*
original attachment (h*i(k*r(w)), j(k*r(w))). The group order
is explicit; no commutativity is assumed.

The remaining Link-specific work is to instantiate the inclusion
squares and iterate these exact charts along an arbitrary component.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w x y z
variable {I : Type u} {G : Type v} {H : Type w}
variable {P : Type x} {Q : Type y} {T : Type z}
variable [Group I] [Group G] [Group H]
variable [Group P] [Group Q] [Group T]

/-- A point of a translated included subgroup coset has a unique
earlier-group coordinate. No finite or abelian group hypothesis. -/
theorem normalized_shift_exists_unique
    (inc : P →* G) (hinj : Function.Injective inc)
    (a target : G)
    (hmem : target ∈ leftCoset inc.range a) :
    ∃! shift : P, a * inc shift = target := by
  change a⁻¹ * target ∈ inc.range at hmem
  obtain ⟨shift, hs⟩ := hmem
  have hshift : a * inc shift = target := by
    rw [hs]
    group
  refine ⟨shift, hshift, ?_⟩
  intro t ht
  apply hinj
  exact mul_left_cancel (ht.trans hshift.symm)

/-- Exact compatibility of normalized OLD-side subgroup attachments.
The shift is on the left because the Cayley blocks use right
multiplication by their generators. -/
theorem normalized_old_boundary
    (common : I →* G) (restricted : P →* G)
    (tripleCommon : T →* I) (tripleOld : T →* P)
    (hsquare : ∀ t : T,
      restricted (tripleOld t) = common (tripleCommon t))
    (h a : G) (k : I) (shift : P)
    (hshift : a * restricted shift = h * common k)
    (t : T) :
    a * restricted (shift * tripleOld t) =
      h * common (k * tripleCommon t) := by
  calc
    a * restricted (shift * tripleOld t) =
        (a * restricted shift) * restricted (tripleOld t) := by
      rw [map_mul]
      group
    _ = (h * common k) * common (tripleCommon t) := by
      rw [hshift, hsquare]
    _ = h * common (k * tripleCommon t) := by
      rw [map_mul]
      group

/-- On the NEW side, choosing the representative at the actual
attaching point j(k) makes the normalized incoming coset
centred at the identity. -/
theorem normalized_new_boundary
    (common : I →* H) (restricted : Q →* H)
    (tripleCommon : T →* I) (tripleNew : T →* Q)
    (hsquare : ∀ t : T,
      restricted (tripleNew t) = common (tripleCommon t))
    (k : I) (t : T) :
    common k * restricted (tripleNew t) =
      common (k * tripleCommon t) := by
  rw [hsquare, map_mul]

end GluingEPPA.Steiner.ChainValuation
