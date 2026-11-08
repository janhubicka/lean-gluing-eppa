import GluingEPPA.Steiner.ChainValuation.GroupAttachment

/-!
# Iterating one exact group attachment

A chain is formed by repeatedly attaching a new Cayley block to the last
embedded block of the previous partial chain. This file validates the generic
set-level induction step: the attachment map into the existing chain is
injective, both sides embed in the new pushout, and their cross-overlap is
exactly the prescribed common subgroup.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w z
variable {K : Type u} {L : Type v} {C : Type w} {Y : Type z}
variable [Group K] [Group L]

/-- Compose a translated subgroup embedding with the embedding of the last
block into the chain already constructed. -/
def attachInto (last : L → C) (h : L) (i : K →* L) : K → C :=
  fun k => last (h * i k)

theorem attachInto_injective
    (last : L → C) (hlast : Function.Injective last)
    (h : L) (i : K →* L) (hi : Function.Injective i) :
    Function.Injective (attachInto last h i) := by
  intro k l hkl
  apply hi
  apply mul_left_cancel (hlast hkl)

/-- The next chain space, obtained by one exact pushout attachment. -/
abbrev ChainExtend
    (last : L → C) (hlast : Function.Injective last)
    (h : L) (i : K →* L) (hi : Function.Injective i)
    (right : K → Y) (hright : Function.Injective right) :=
  SetPushout (attachInto last h i) right
    (attachInto_injective last hlast h i hi) hright

/-- Everything in the previously constructed chain remains distinct. -/
theorem chainExtend_old_injective
    (last : L → C) (hlast : Function.Injective last)
    (h : L) (i : K →* L) (hi : Function.Injective i)
    (right : K → Y) (hright : Function.Injective right) :
    Function.Injective
      (pushoutInl (attachInto last h i) right
        (attachInto_injective last hlast h i hi) hright) :=
  pushoutInl_injective _ _ _ _

/-- The newly attached block also embeds. -/
theorem chainExtend_new_injective
    (last : L → C) (hlast : Function.Injective last)
    (h : L) (i : K →* L) (hi : Function.Injective i)
    (right : K → Y) (hright : Function.Injective right) :
    Function.Injective
      (pushoutInr (attachInto last h i) right
        (attachInto_injective last hlast h i hi) hright) :=
  pushoutInr_injective _ _ _ _

/-- Cross-side equality in one extension is exactly one point of the prescribed
attachment subgroup. -/
theorem chainExtend_overlap_iff
    (last : L → C) (hlast : Function.Injective last)
    (h : L) (i : K →* L) (hi : Function.Injective i)
    (right : K → Y) (hright : Function.Injective right)
    (x : C) (y : Y) :
    pushoutInl (attachInto last h i) right
        (attachInto_injective last hlast h i hi) hright x =
      pushoutInr (attachInto last h i) right
        (attachInto_injective last hlast h i hi) hright y ↔
      ∃ k, last (h * i k) = x ∧ right k = y :=
  pushoutInl_eq_inr_iff _ _ _ _ _ _

end GluingEPPA.Steiner.ChainValuation
