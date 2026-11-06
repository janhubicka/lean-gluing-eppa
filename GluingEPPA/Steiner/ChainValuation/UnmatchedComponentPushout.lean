import GluingEPPA.Steiner.ChainValuation.MatchedComponentPushout

/-!
# Components which miss the attaching interface

An old M-component disjoint from the attaching interface survives an
injective pushout as exactly one full quotient M-component. The symmetric
claim holds for an unattached new component.

There is NO compatibility assumption in these statements: a path
could only cross the interface through a vertex in the corresponding
component, which is excluded. The proof uses the genuine labelled
path-to-gluing equivalence, including paths with reversals.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w t
variable {E : Type u} {X : Type v} {Y : Type w} {Z : Type t}

/-- A full old component that does not touch the interface remains
exactly the same component after attaching the new labelled graph. -/
theorem unmatchedOldComponent_iff_reach
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (q : X) (hnomeet : ∀ z : Z, ¬ LabelReach R M q (f z))
    (v : SetPushout f g hf hg) :
    LabelReach (pushoutLabelRel R T f g hf hg) M
      (pushoutInl f g hf hg q) v ↔
    ∃ x : X, LabelReach R M q x ∧ pushoutInl f g hf hg x = v := by
  let P : Sum X Y → Prop := fun a =>
    match a with
    | .inl x => LabelReach R M q x
    | .inr _ => False
  have hpreserve : ∀ {a b : Sum X Y},
      GluedReach (labelReachSetoid R M) (labelReachSetoid T M)
        f g a b → (P a ↔ P b) := by
    intro a b h
    induction h with
    | refl a => exact Iff.rfl
    | old h =>
        constructor
        · intro hx
          exact LabelReach.trans hx h
        · intro hy
          exact LabelReach.trans hy (LabelReach.symm h)
    | new h => exact Iff.rfl
    | attach z =>
        constructor
        · intro hx
          exact False.elim (hnomeet z hx)
        · intro hy
          exact False.elim hy
    | symm h ih => exact ih.symm
    | trans h k ih ik => exact ih.trans ik
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := pushoutPoint_surjective f g hf hg v
    rw [← ha] at hv
    have hglue :
        GluedReach (labelReachSetoid R M) (labelReachSetoid T M)
          f g (.inl q) a :=
      (pushoutReach_iff_gluedReach R T M f g hf hg
        (.inl q) a).mp hv
    have hp : P a := (hpreserve hglue).mp (LabelReach.refl q)
    cases a with
    | inl x => exact ⟨x, hp, ha⟩
    | inr y => exact False.elim hp
  · rintro ⟨x, hr, hx⟩
    rw [← hx]
    exact gluedReach_to_pushoutReach R T M f g hf hg
      (GluedReach.old hr)

/-- The symmetric statement for an unattached new component. -/
theorem unmatchedNewComponent_iff_reach
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (q : Y) (hnomeet : ∀ z : Z, ¬ LabelReach T M q (g z))
    (v : SetPushout f g hf hg) :
    LabelReach (pushoutLabelRel R T f g hf hg) M
      (pushoutInr f g hf hg q) v ↔
    ∃ y : Y, LabelReach T M q y ∧ pushoutInr f g hf hg y = v := by
  let P : Sum X Y → Prop := fun a =>
    match a with
    | .inl _ => False
    | .inr y => LabelReach T M q y
  have hpreserve : ∀ {a b : Sum X Y},
      GluedReach (labelReachSetoid R M) (labelReachSetoid T M)
        f g a b → (P a ↔ P b) := by
    intro a b h
    induction h with
    | refl a => exact Iff.rfl
    | old h => exact Iff.rfl
    | new h =>
        constructor
        · intro hx
          exact LabelReach.trans hx h
        · intro hy
          exact LabelReach.trans hy (LabelReach.symm h)
    | attach z =>
        constructor
        · intro hx
          exact False.elim hx
        · intro hy
          exact False.elim (hnomeet z hy)
    | symm h ih => exact ih.symm
    | trans h k ih ik => exact ih.trans ik
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := pushoutPoint_surjective f g hf hg v
    rw [← ha] at hv
    have hglue :
        GluedReach (labelReachSetoid R M) (labelReachSetoid T M)
          f g (.inr q) a :=
      (pushoutReach_iff_gluedReach R T M f g hf hg
        (.inr q) a).mp hv
    have hp : P a := (hpreserve hglue).mp (LabelReach.refl q)
    cases a with
    | inl x => exact False.elim hp
    | inr y => exact ⟨y, hp, ha⟩
  · rintro ⟨y, hr, hy⟩
    rw [← hy]
    exact gluedReach_to_pushoutReach R T M f g hf hg
      (GluedReach.new hr)

end GluingEPPA.Steiner.ChainValuation
