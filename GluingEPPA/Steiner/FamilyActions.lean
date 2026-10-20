import GluingEPPA.Steiner.FamilyProjections

/-!
# Compatible actions of the old groups on every old quotient

The old groups were constructed on smaller edge sets. They retain embeddings,
deletions, and exact walk membership. Every old group acts on quotients indexed
by its own proper edge subsets. The crossing-subset lemma extends those actions
to all the quotient coordinates used at the next product stage.

This closes the compatibility premise of `StepAssembly` in terms of actual
older-stage data. The recursive construction of the family itself is separate.
-/

namespace GluingEPPA.Steiner.RecursiveStep

universe u v w z
variable {I : Type u} {V : Type v} {E : Type w}
variable (A : I → Type z) [∀ i, Group (A i)]
variable (T : ∀ i, Transport V (A i))
variable (R : I → Set E) (a : ∀ i, E → A i)
variable (D : EdgeGraph V E)
variable (F : OldGroupMaps A R a)

/-- Available properties of groups already constructed on smaller masks.
The restriction action is needed only at a mask strictly below the source,
represented here by `meet r t` when `R r` is not contained in `R t`. -/
structure OldWalkActions where
  inclusion_injective :
    ∀ r t (h : R r ⊆ R t), Function.Injective (F.inclusion r t h)
  preserves :
    ∀ r t (h : R r ⊆ R t) u v g,
      (T r).Rel u v g →
      (T t).Rel u v (F.inclusion r t h g)
  replacement :
    ∀ r t (h : R r ⊆ R t) u v g,
      (T t).Rel u v (F.inclusion r t h g) →
      ∃ k, (T r).Rel u v k ∧
        F.inclusion r t h k = F.inclusion r t h g
  involutive : ∀ r e, e ∈ R r → a r e * a r e = 1
  generated : ∀ r g, ∃ w : List (R r),
    wordValue (fun e : R r => a r e.val) w = g
  smallerAction : ∀ r t, (¬ R r ⊆ R t) →
    A r →* Equiv.Perm ((T (F.meet r t)).Space)
  smallerAction_generator : ∀ r t (h : ¬ R r ⊆ R t) (e : R r),
    smallerAction r t h (a r e.val) =
      (T (F.meet r t)).edgePerm D (R (F.meet r t))
        (a (F.meet r t)) e.val

namespace OldWalkActions

variable (C : OldWalkActions A T R a D F)

/-- Every old group acts on every quotient used by the new product.
For crossing masks the checked restriction theorem is applied to the
existing action on the intersection mask. -/
noncomputable def actionWithGenerators (r t : I) :
    { φ : A r →* Equiv.Perm ((T t).Space) //
      ∀ e : R r, φ (a r e.val) =
        (T t).edgePerm D (R t) (a t) e.val } := by
  classical
  by_cases hsub : R r ⊆ R t
  · refine ⟨(T t).action.comp (F.inclusion r t hsub), ?_⟩
    intro e
    change (T t).action (F.inclusion r t hsub (a r e.val)) =
      (T t).edgePerm D (R t) (a t) e.val
    rw [F.inclusion_generator r t hsub e.val e.property]
    simp [Transport.edgePerm, hsub e.property]
  · let l := F.meet r t
    have hlt : R l ⊆ R t := F.meet_subset_right r t
    let i : A l →* A t := F.inclusion l t hlt
    have hon : ∀ e : R r, e.val ∈ R t →
        C.smallerAction r t hsub (a r e.val) =
          (T l).action (a l e.val) := by
      intro e ht
      have hl : e.val ∈ R l := by
        rw [F.meet_eq]
        exact ⟨e.property, ht⟩
      rw [C.smallerAction_generator r t hsub e]
      simp [Transport.edgePerm, hl]
    have hout : ∀ e : R r, ¬ e.val ∈ R t →
        C.smallerAction r t hsub (a r e.val) =
          (T l).swapPoints (D.source e.val) (D.target e.val) := by
      intro e ht
      have hl : e.val ∉ R l := by
        rw [F.meet_eq]
        exact fun h => ht h.2
      rw [C.smallerAction_generator r t hsub e]
      simp [Transport.edgePerm, hl]
    have hdel : ∀ e : R r, e.val ∈ R t →
        F.deletion r t (a r e.val) = a l e.val := by
      intro e ht
      rw [F.deletion_generator r t e.val e.property]
      simp [ht]
    have hdelout : ∀ e : R r, ¬ e.val ∈ R t →
        F.deletion r t (a r e.val) = 1 := by
      intro e ht
      rw [F.deletion_generator r t e.val e.property]
      simp [ht]
    obtain ⟨φ, hφ⟩ := (T t).restriction_factors
      (T l) i (C.preserves l t hlt)
      ((T t).reflects_of_membership (T l) i
        (C.inclusion_injective l t hlt) (C.replacement l t hlt))
      (fun e : R r => a r e.val)
      (fun e : R r => a l e.val)
      (fun e : R r => e.val ∈ R t)
      (fun e : R r => D.source e.val)
      (fun e : R r => D.target e.val)
      (C.smallerAction r t hsub)
      (F.deletion r t)
      hon hout hdel hdelout
      (fun e => C.involutive r e.val e.property)
      (C.generated r)
    refine ⟨φ, ?_⟩
    intro e
    rw [hφ e]
    by_cases ht : e.val ∈ R t
    · have hl : e.val ∈ R l := by
        rw [F.meet_eq]
        exact ⟨e.property, ht⟩
      have hi : i (a l e.val) = a t e.val :=
        F.inclusion_generator l t hlt e.val hl
      simp [Transport.restrictedEdge, Transport.edgePerm, ht, hi]
    · simp [Transport.restrictedEdge, Transport.edgePerm, ht]

/-- The two coordinate kinds satisfy exactly the assumptions of the
previously checked finite product construction. -/
noncomputable def compatible : CompatibleCoordinates A T R a D where
  groups := F.groupCoordinate
  actions := fun r t => (C.actionWithGenerators r t).val
  groups_on := by
    intro r e t
    exact F.groupCoordinate_generator r t e.val e.property
  actions_on := by
    intro r e t
    exact (C.actionWithGenerators r t).property e

end OldWalkActions
end GluingEPPA.Steiner.RecursiveStep
