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

def pushoutRel (f : Z → X) (g : Z → Y) : Sum X Y → Sum X Y → Prop
  | .inl x, .inl x' => x = x'
  | .inr y, .inr y' => y = y'
  | .inl x, .inr y => ∃ z, f z = x ∧ g z = y
  | .inr y, .inl x => ∃ z, g z = y ∧ f z = x

def pushoutSetoid (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Setoid (Sum X Y) where
  r := pushoutRel f g
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      cases a <;> rfl
    · intro a b hab
      cases a with
      | inl x =>
        cases b with
        | inl y => exact hab.symm
        | inr y =>
          rcases hab with ⟨z, hzX, hzY⟩
          exact ⟨z, hzY, hzX⟩
      | inr x =>
        cases b with
        | inl y =>
          rcases hab with ⟨z, hzX, hzY⟩
          exact ⟨z, hzY, hzX⟩
        | inr y => exact hab.symm
    · intro a b c hab hbc
      cases a with
      | inl x =>
        cases b with
        | inl y =>
          cases c with
          | inl z => exact hab.trans hbc
          | inr z =>
            rcases hbc with ⟨k, hkY, hkZ⟩
            exact ⟨k, hkY.trans hab.symm, hkZ⟩
        | inr y =>
          cases c with
          | inl z =>
            rcases hab with ⟨k, hkX, hkY⟩
            rcases hbc with ⟨l, hlY, hlZ⟩
            have hkl : k = l := hg (hkY.trans hlY.symm)
            subst l
            exact hkX.symm.trans hlZ
          | inr z =>
            rcases hab with ⟨k, hkX, hkY⟩
            exact ⟨k, hkX, hkY.trans hbc⟩
      | inr x =>
        cases b with
        | inl y =>
          cases c with
          | inl z =>
            rcases hab with ⟨k, hkX, hkY⟩
            exact ⟨k, hkX, hkY.trans hbc⟩
          | inr z =>
            rcases hab with ⟨k, hkX, hkY⟩
            rcases hbc with ⟨l, hlY, hlZ⟩
            have hkl : k = l := hf (hkY.trans hlY.symm)
            subst l
            exact hkX.symm.trans hlZ
        | inr y =>
          cases c with
          | inl z =>
            rcases hbc with ⟨k, hkY, hkZ⟩
            exact ⟨k, hkY.trans hab.symm, hkZ⟩
          | inr z => exact hab.trans hbc

abbrev SetPushout (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :=
  Quotient (pushoutSetoid f g hf hg)

def pushoutInl (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    X → SetPushout f g hf hg :=
  fun x => Quotient.mk (pushoutSetoid f g hf hg) (Sum.inl x)

def pushoutInr (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Y → SetPushout f g hf hg :=
  fun y => Quotient.mk (pushoutSetoid f g hf hg) (Sum.inr y)

theorem pushoutInl_injective (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (pushoutInl f g hf hg) := by
  intro x x' h
  change Quotient.mk (pushoutSetoid f g hf hg) (Sum.inl x) =
    Quotient.mk (pushoutSetoid f g hf hg) (Sum.inl x') at h
  exact Quotient.exact h

theorem pushoutInr_injective (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (pushoutInr f g hf hg) := by
  intro y y' h
  change Quotient.mk (pushoutSetoid f g hf hg) (Sum.inr y) =
    Quotient.mk (pushoutSetoid f g hf hg) (Sum.inr y') at h
  exact Quotient.exact h

theorem pushoutInl_eq_inr_iff (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (x : X) (y : Y) :
    pushoutInl f g hf hg x = pushoutInr f g hf hg y ↔
      ∃ z, f z = x ∧ g z = y := by
  constructor
  · intro h
    change Quotient.mk (pushoutSetoid f g hf hg) (Sum.inl x) =
      Quotient.mk (pushoutSetoid f g hf hg) (Sum.inr y) at h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

@[simp] theorem pushout_attachment (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g) (z : Z) :
    pushoutInl f g hf hg (f z) = pushoutInr f g hf hg (g z) := by
  exact Quotient.sound ⟨z, rfl, rfl⟩

end GluingEPPA.Steiner.ChainValuation
