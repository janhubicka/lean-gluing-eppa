import Mathlib

/-!
# Completing a partial matching to an involutive permutation

The chain letter action is the union of labelled Cayley edges from its blocks.
Once this relation is symmetric and has at most one neighbour at each vertex,
unmatched vertices may be fixed canonically.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u
variable {X : Type u}

/-- A symmetric relation with at most one neighbour at every point. -/
structure Matching (X : Type u) where
  Rel : X → X → Prop
  symm : ∀ {x y}, Rel x y → Rel y x
  unique : ∀ {x y z}, Rel x y → Rel x z → y = z

namespace Matching

attribute [local instance] Classical.propDecidable

noncomputable def next (M : Matching X) (x : X) : X :=
  if h : ∃ y, M.Rel x y then Classical.choose h else x

theorem next_eq_of_rel (M : Matching X) {x y : X} (hxy : M.Rel x y) :
    M.next x = y := by
  unfold next
  split
  next h =>
    exact M.unique (Classical.choose_spec h) hxy
  next h =>
    exact False.elim (h ⟨y, hxy⟩)

theorem next_eq_self_of_none (M : Matching X) {x : X}
    (h : ¬ ∃ y, M.Rel x y) : M.next x = x := by
  simp [next, h]

theorem next_involutive (M : Matching X) : Function.Involutive M.next := by
  intro x
  by_cases h : ∃ y, M.Rel x y
  · let y := Classical.choose h
    have hxy : M.Rel x y := Classical.choose_spec h
    rw [M.next_eq_of_rel hxy, M.next_eq_of_rel (M.symm hxy)]
  · rw [M.next_eq_self_of_none h, M.next_eq_self_of_none h]

/-- Complete the matching by fixing exactly the unmatched points. -/
noncomputable def perm (M : Matching X) : Equiv.Perm X where
  toFun := M.next
  invFun := M.next
  left_inv := M.next_involutive
  right_inv := M.next_involutive

@[simp] theorem perm_apply (M : Matching X) (x : X) :
    M.perm x = M.next x := rfl

theorem perm_eq_of_rel (M : Matching X) {x y : X} (hxy : M.Rel x y) :
    M.perm x = y :=
  M.next_eq_of_rel hxy

theorem perm_fixed_of_none (M : Matching X) {x : X}
    (h : ¬ ∃ y, M.Rel x y) : M.perm x = x :=
  M.next_eq_self_of_none h

end Matching
end GluingEPPA.Steiner.ChainValuation
