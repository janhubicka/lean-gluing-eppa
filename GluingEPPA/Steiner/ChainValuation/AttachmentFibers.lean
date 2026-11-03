import GluingEPPA.Steiner.ChainValuation.TwoGroupRestriction

/-!
# Exact fibres of restricted cosets at an attachment

The no-merging result is not enough to classify the restricted components:
we also need to know that the *whole* attaching set between two pieces is a
coset of the common restricted subgroup, rather than an arbitrary nonempty
subset. We prove this for two unrelated groups over an earlier common group.

No ambient full-stage group, finiteness or commutativity is assumed.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {H : Type u} {G : Type v} {K : Type w}
variable [Group H] [Group G] [Group K]

/-- The pullback of a translated restricted coset along an attaching map is
exactly a coset of the pullback subgroup. In particular the attachment meets
a restricted piece in one *whole* subgroup coset. -/
theorem attachment_fiber_coset
    (i : H →* G) (P : Subgroup G) (h : G) (k : H) :
    {z : H | h * i z ∈ leftCoset P (h * i k)} =
      leftCoset (P.comap i) k := by
  ext z
  change (h * i k)⁻¹ * (h * i z) ∈ P ↔
    i (k⁻¹ * z) ∈ P
  have hid : (h * i k)⁻¹ * (h * i z) = i (k⁻¹ * z) := by
    simp only [map_mul, map_inv]
    group
  rw [hid]

/-- Two restricted coset pieces in distinct blocks have the same attaching
fibre if their pulled-back subgroups agree. The equality is on the *common
group*, so it preserves all attachment vertices, not merely their existence. -/
theorem two_group_attachment_fiber
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K)
    (hcomap : P.comap i = Q.comap j)
    (h : G) (k : H) :
    {z : H | h * i z ∈ leftCoset P (h * i k)} =
      {z : H | j z ∈ leftCoset Q (j k)} := by
  rw [attachment_fiber_coset]
  calc
    leftCoset (P.comap i) k = leftCoset (Q.comap j) k := by rw [hcomap]
    _ = {z : H | j z ∈ leftCoset Q (j k)} := by
      simpa only [one_mul] using
        (attachment_fiber_coset j Q (1 : K) k).symm

/-- Membership is preserved pointwise across a common attachment; no
correspondence of arbitrary coset representatives is chosen. -/
theorem two_group_attachment_mem_iff
    (i : H →* G) (j : H →* K)
    (P : Subgroup G) (Q : Subgroup K)
    (hcomap : P.comap i = Q.comap j)
    (h : G) (k z : H) :
    h * i z ∈ leftCoset P (h * i k) ↔
      j z ∈ leftCoset Q (j k) := by
  have heq := two_group_attachment_fiber i j P Q hcomap h k
  exact Set.ext_iff.mp heq z

/-- A restricted piece meets the attaching coset precisely in the image of
the coset of its intersection subgroup in the common group. -/
theorem attachment_intersection_exact
    (i : H →* G) (P : Subgroup G) (h : G) (k : H) :
    leftCoset P (h * i k) ∩ leftCoset i.range h =
      {x : G | ∃ z : H,
        z ∈ leftCoset (P.comap i) k ∧ x = h * i z} := by
  ext x
  constructor
  · rintro ⟨hp, hi⟩
    change h⁻¹ * x ∈ i.range at hi
    obtain ⟨z, hz⟩ := hi
    refine ⟨z, ?_, ?_⟩
    · have hf := attachment_fiber_coset i P h k
      change z ∈ leftCoset (P.comap i) k
      rw [← hf]
      change (h * i k)⁻¹ * (h * i z) ∈ P
      have heqx : x = h * i z := by
        calc
          x = h * (h⁻¹ * x) := by group
          _ = h * i z := by rw [hz]
      change (h * i k)⁻¹ * x ∈ P at hp
      rwa [heqx] at hp
    · calc
        x = h * (h⁻¹ * x) := by group
        _ = h * i z := by rw [hz]
  · rintro ⟨z, hz, rfl⟩
    constructor
    · have hf := attachment_fiber_coset i P h k
      exact (Set.ext_iff.mp hf z).2 hz
    · change h⁻¹ * (h * i z) ∈ i.range
      simpa using (show i z ∈ i.range from ⟨z, rfl⟩)

end GluingEPPA.Steiner.ChainValuation
