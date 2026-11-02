import Mathlib

/-!
# Set pushouts along two injections

A separated chain is built by repeatedly gluing a new block to the preceding
union along one injective attachment. This file supplies the exact set-level
pushout: both sides embed, and cross-side equality is precisely the prescribed
attachment relation.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The explicit equivalence relation for a pushout of two injections. -/
def pushoutRel (f : Z → X) (g : Z → Y) : Sum X Y → Sum X Y → Prop
  | .inl x, .inl x' => x = x'
  | .inr y, .inr y' => y = y'
  | .inl x, .inr y => ∃ z, f z = x ∧ g z = y
  | .inr y, .inl x => ∃ z, g z = y ∧ f z = x

/-- For injective attaching maps, the explicit relation is already an
equivalence relation; no further transitive closure creates identifications. -/
def pushoutSetoid (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Setoid (Sum X Y) where
  r := pushoutRel f g
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      cases a <;> simp [pushoutRel]
    · intro a b h
      cases a <;> cases b <;> simp [pushoutRel] at h ⊢ <;> aesop
    · intro a b c hab hbc
      cases a <;> cases b <;> cases c <;>
        simp [pushoutRel] at hab hbc ⊢ <;> aesop

/-- The set pushout. -/
abbrev SetPushout (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :=
  Quotient (pushoutSetoid f g hf hg)

def pushoutInl (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    X → SetPushout f g hf hg :=
  fun x => Quotient.mk' (Sum.inl x)

def pushoutInr (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Y → SetPushout f g hf hg :=
  fun y => Quotient.mk' (Sum.inr y)

theorem pushoutInl_injective (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (pushoutInl f g hf hg) := by
  intro x x' h
  exact Quotient.exact h

theorem pushoutInr_injective (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (pushoutInr f g hf hg) := by
  intro y y' h
  exact Quotient.exact h

/-- Cross-side equality is exactly one prescribed attachment. -/
theorem pushoutInl_eq_inr_iff (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (x : X) (y : Y) :
    pushoutInl f g hf hg x = pushoutInr f g hf hg y ↔
      ∃ z, f z = x ∧ g z = y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

@[simp] theorem pushout_attachment (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) (z : Z) :
    pushoutInl f g hf hg (f z) = pushoutInr f g hf hg (g z) :=
  Quotient.sound ⟨z, rfl, rfl⟩

end GluingEPPA.Steiner.ChainValuation
