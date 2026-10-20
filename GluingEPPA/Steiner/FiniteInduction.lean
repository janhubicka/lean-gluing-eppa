import GluingEPPA.Steiner.FiniteStep

/-!
# Compatibility and walk replacement for the recursively defined finite family

The induction is over proper finite edge subsets. Its conclusion refers to the
single family defined in `FiniteFamily`, so different uses of the same subset
retain literally the same group. No compatible family is an external premise.
-/

namespace GluingEPPA.Steiner.FiniteFamily

universe u
variable {V E : Type u} [Fintype E] [DecidableEq E] [Finite V]
attribute [local instance] Classical.propDecidable

abbrev previous (D : EdgeGraph V E) (S : Finset E) (r : Proper S) := family D r.val

abbrev Good (D : EdgeGraph V E) (S : Finset E) :=
  Correct D S (family D S) (previous D S)

namespace Good

variable (D : EdgeGraph V E) (S : Finset E) (c : Good D S)

/-- Include any subset; equality of the two subsets uses the identity map. -/
noncomputable def incAll (R : Finset E) (h : R ⊆ S) :
    (family D R).Carrier →* (family D S).Carrier := by
  classical
  by_cases he : R = S
  · subst R
    exact MonoidHom.id _
  · exact c.inc ⟨R, Finset.ssubset_iff_subset_ne.mpr ⟨h, he⟩⟩

noncomputable def retAll (R : Finset E) (h : R ⊆ S) :
    (family D S).Carrier →* (family D R).Carrier := by
  classical
  by_cases he : R = S
  · subst R
    exact MonoidHom.id _
  · exact c.ret ⟨R, Finset.ssubset_iff_subset_ne.mpr ⟨h, he⟩⟩

theorem incAll_edge (R : Finset E) (h : R ⊆ S) (e : E) (he : e ∈ R) :
    incAll D S c R h ((family D R).edge e) = (family D S).edge e := by
  by_cases hEq : R = S
  · subst R
    simp [incAll]
  · simpa only [incAll, dif_neg hEq] using
      c.inc_edge ⟨R, Finset.ssubset_iff_subset_ne.mpr ⟨h, hEq⟩⟩ e he

theorem retAll_edge (R : Finset E) (h : R ⊆ S) (e : E) (he : e ∈ S) :
    retAll D S c R h ((family D S).edge e) =
      if e ∈ R then (family D R).edge e else 1 := by
  by_cases hEq : R = S
  · subst R
    simp [retAll, he]
  · simpa only [retAll, dif_neg hEq] using
      c.ret_edge ⟨R, Finset.ssubset_iff_subset_ne.mpr ⟨h, hEq⟩⟩ e he

theorem retAll_leftInverse (R : Finset E) (h : R ⊆ S) :
    Function.LeftInverse (retAll D S c R h) (incAll D S c R h) := by
  by_cases hEq : R = S
  · subst R
    intro g
    simp [retAll, incAll]
  · simpa only [retAll, incAll, dif_neg hEq] using
      c.left_inverse ⟨R, Finset.ssubset_iff_subset_ne.mpr ⟨h, hEq⟩⟩

theorem incAll_injective (R : Finset E) (h : R ⊆ S) :
    Function.Injective (incAll D S c R h) :=
  (retAll_leftInverse D S c R h).injective

theorem preserves (R : Finset E) (h : R ⊆ S) (u v : V)
    (g : (family D R).Carrier)
    (p : D.WalkValue (↑R : Set E) (family D R).edge u v g) :
    D.WalkValue (↑S : Set E) (family D S).edge u v (incAll D S c R h g) := by
  exact p.mapOn (incAll D S c R h) (fun _ he => h he)
    (fun e he => incAll_edge D S c R h e he)

theorem replacement (R : Finset E) (h : R ⊆ S) (u v : V)
    (g : (family D R).Carrier)
    (p : D.WalkValue (↑S : Set E) (family D S).edge u v (incAll D S c R h g)) :
    D.WalkValue (↑R : Set E) (family D R).edge u v g := by
  by_cases hEq : R = S
  · subst R
    simpa only [incAll, dif_pos rfl, MonoidHom.id_apply] using p
  · apply c.replacement ⟨R, Finset.ssubset_iff_subset_ne.mpr ⟨h, hEq⟩⟩ u v g
    simpa only [incAll, dif_neg hEq] using p

end Good

namespace Older

variable (D : EdgeGraph V E) (S : Finset E) (ih : ∀ r : Proper S, Good D r.val)

/-- Intersections remain proper subsets of the current set. -/
def meet (r t : Proper S) : Proper S :=
  ⟨r.val ∩ t.val, Finset.ssubset_of_subset_of_ssubset Finset.inter_subset_left r.property⟩

theorem meet_eq (r t : Proper S) :
    (↑(meet S r t).val : Set E) = (↑r.val : Set E) ∩ ↑t.val := by
  ext e
  simp [meet]

theorem meet_lt_left (r t : Proper S)
    (h : ¬ (↑r.val : Set E) ⊆ ↑t.val) : (meet S r t).val ⊂ r.val := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.inter_subset_left, ?_⟩
  intro heq
  apply h
  intro e he
  have hm : e ∈ (meet S r t).val := by rw [heq]; exact he
  exact (Finset.mem_inter.mp hm).2

noncomputable def maps : RecursiveStep.OldGroupMaps
    (Step.Groups S (previous D S)) (Step.masks S) (Step.edges S (previous D S)) where
  meet := meet S
  meet_eq := meet_eq S
  inclusion := fun r t h => Good.incAll D t.val (ih t) r.val h
  inclusion_generator := by
    intro r t h e he
    exact Good.incAll_edge D t.val (ih t) r.val h e he
  deletion := fun r t => Good.retAll D r.val (ih r) (meet S r t).val Finset.inter_subset_left
  deletion_generator := by
    intro r t e he
    rw [Good.retAll_edge D r.val (ih r) (meet S r t).val Finset.inter_subset_left e he]
    by_cases ht : e ∈ t.val
    · have hm : e ∈ (meet S r t).val := Finset.mem_inter.mpr ⟨he, ht⟩
      simp only [ite_eq_left hm, ite_eq_left ht]
    · have hm : e ∉ (meet S r t).val := fun h => ht (Finset.mem_inter.mp h).2
      simp only [ite_eq_right hm, ite_eq_right ht]

noncomputable def actions : RecursiveStep.OldWalkActions
    (Step.Groups S (previous D S)) (Step.transports D S (previous D S))
    (Step.masks S) (Step.edges S (previous D S)) D (maps D S ih) where
  inclusion_injective := by
    intro r t h
    exact Good.incAll_injective D t.val (ih t) r.val h
  preserves := by
    intro r t h u v g p
    exact Good.preserves D t.val (ih t) r.val h u v g p
  replacement := by
    intro r t h u v g p
    exact ⟨g, Good.replacement D t.val (ih t) r.val h u v g p, rfl⟩
  involutive := fun r e _ => (family D r.val).involutive e
  generated := fun r => (family D r.val).generated
  smallerAction := fun r t h =>
    (ih r).action ⟨(meet S r t).val, meet_lt_left S r t h⟩
  smallerAction_generator := by
    intro r t h e
    exact (ih r).action_edge ⟨(meet S r t).val, meet_lt_left S r t h⟩ e.val e.property

noncomputable def compatible : RecursiveStep.CompatibleCoordinates
    (Step.Groups S (previous D S)) (Step.transports D S (previous D S))
    (Step.masks S) (Step.edges S (previous D S)) D :=
  RecursiveStep.OldWalkActions.compatible
    (Step.Groups S (previous D S)) (Step.transports D S (previous D S))
    (Step.masks S) (Step.edges S (previous D S)) D (maps D S ih) (actions D S ih)

end Older

/-- The complete induction. Every hypothesis supplied to `Older.compatible`
comes from a strict subset of the current set. -/
noncomputable def good (D : EdgeGraph V E) : (S : Finset E) → Good D S :=
  Finset.strongInduction fun S ih => by
    change Correct D S (family D S) (previous D S)
    rw [family_eq D S]
    exact Step.correct D S (previous D S)
      (Older.compatible D S (fun r => ih r.val r.property))

noncomputable def inclusion (D : EdgeGraph V E) (R S : Finset E) (h : R ⊆ S) :
    (family D R).Carrier →* (family D S).Carrier :=
  Good.incAll D S (good D S) R h

noncomputable def retraction (D : EdgeGraph V E) (R S : Finset E) (h : R ⊆ S) :
    (family D S).Carrier →* (family D R).Carrier :=
  Good.retAll D S (good D S) R h

theorem inclusion_injective (D : EdgeGraph V E) (R S : Finset E) (h : R ⊆ S) :
    Function.Injective (inclusion D R S h) :=
  Good.incAll_injective D S (good D S) R h

theorem retraction_inclusion (D : EdgeGraph V E) (R S : Finset E) (h : R ⊆ S) :
    Function.LeftInverse (retraction D R S h) (inclusion D R S h) :=
  Good.retAll_leftInverse D S (good D S) R h

/-- Unconditional same-value replacement for the actual finite family. -/
theorem replaceWalk (D : EdgeGraph V E) (R S : Finset E) (h : R ⊆ S)
    (u v : V) (g : (family D R).Carrier)
    (p : D.WalkValue (↑S : Set E) (family D S).edge u v (inclusion D R S h g)) :
    D.WalkValue (↑R : Set E) (family D R).edge u v g :=
  Good.replacement D S (good D S) R h u v g p

end GluingEPPA.Steiner.FiniteFamily
