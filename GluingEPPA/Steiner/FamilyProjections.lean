import GluingEPPA.Steiner.StepAssembly

/-!
# The old group coordinates for the Steiner finite recursion

For an indexed family of previously constructed edge subsets, inclusions and
deletion maps assemble a map from each old group to every old group coordinate
of the next product. This module does not assume the desired compatibility
maps: it constructs them and verifies their effect on every named generator.

The group actions on the old quotient coordinates are handled separately.
-/

namespace GluingEPPA.Steiner.RecursiveStep

universe u v w z
attribute [local instance] Classical.propDecidable
variable {I : Type u} {E : Type v}
variable (A : I → Type w) [∀ i, Group (A i)]
variable (R : I → Set E) (a : ∀ i, E → A i)

/-- Existing inclusions and deletions on smaller edge subsets. -/
structure OldGroupMaps where
  meet : I → I → I
  meet_eq : ∀ r t, R (meet r t) = R r ∩ R t
  inclusion : ∀ r t, R r ⊆ R t → A r →* A t
  inclusion_generator : ∀ r t (h : R r ⊆ R t) e, e ∈ R r →
    inclusion r t h (a r e) = a t e
  deletion : ∀ r t, A r →* A (meet r t)
  deletion_generator : ∀ r t e, e ∈ R r →
    deletion r t (a r e) =
      if e ∈ R t then a (meet r t) e else 1

namespace OldGroupMaps

variable (F : OldGroupMaps A R a)

/-- Every mask intersection is a subset of the second mask. -/
theorem meet_subset_right (r t : I) : R (F.meet r t) ⊆ R t := by
  rw [F.meet_eq]
  exact Set.inter_subset_right

theorem meet_subset_left (r t : I) : R (F.meet r t) ⊆ R r := by
  rw [F.meet_eq]
  exact Set.inter_subset_left

/-- Retain precisely the generators belonging to the target mask. -/
def groupCoordinate (r t : I) : A r →* A t :=
  (F.inclusion (F.meet r t) t (OldGroupMaps.meet_subset_right A R a F r t)).comp
    (F.deletion r t)

/-- This is the group-coordinate identity needed by the next finite product. -/
theorem groupCoordinate_generator (r t : I) (e : E) (he : e ∈ R r) :
    OldGroupMaps.groupCoordinate A R a F r t (a r e) =
      if e ∈ R t then a t e else 1 := by
  change F.inclusion (F.meet r t) t (OldGroupMaps.meet_subset_right A R a F r t)
    (F.deletion r t (a r e)) =
      if e ∈ R t then a t e else 1
  rw [F.deletion_generator r t e he]
  by_cases ht : e ∈ R t
  · have hm : e ∈ R (F.meet r t) := by
      rw [F.meet_eq]
      exact ⟨he, ht⟩
    simp only [ite_eq_left ht]
    exact F.inclusion_generator (F.meet r t) t
      (OldGroupMaps.meet_subset_right A R a F r t) e hm
  · simp [ht]

end OldGroupMaps
end GluingEPPA.Steiner.RecursiveStep
