import GluingEPPA.Steiner.ChainValuation.LayerMatch
import GluingEPPA.Steiner.ChainValuation.MatchingComponents

/-!
# Passing from restricted attachment matchings to layered path components

Each adjacent pair of layers already carries a symmetric matching. The
forward and backward optional transports are exact inverses on their domains,
so the layer-root theorem can be applied without choosing global components.
-/

namespace GluingEPPA.Steiner.ChainValuation

attribute [local instance] Classical.propDecidable

universe u v
variable {X : Type u} {Y : Type v}

/-- The unique right neighbour of a left piece, if one exists. -/
noncomputable def Matching.forwardOption (M : Matching (Sum X Y)) (x : X) :
    Option Y :=
  if h : ∃ y, M.Rel (.inl x) (.inr y) then some (Classical.choose h) else none

/-- The unique left neighbour of a right piece, if one exists. -/
noncomputable def Matching.backwardOption (M : Matching (Sum X Y)) (y : Y) :
    Option X :=
  if h : ∃ x, M.Rel (.inr y) (.inl x) then some (Classical.choose h) else none

theorem Matching.forwardOption_eq_some_iff (M : Matching (Sum X Y))
    (x : X) (y : Y) :
    M.forwardOption x = some y ↔ M.Rel (.inl x) (.inr y) := by
  classical
  by_cases h : ∃ z, M.Rel (.inl x) (.inr z)
  · simp only [forwardOption, dif_pos h, Option.some.injEq]
    constructor
    · intro hxy
      subst y
      exact Classical.choose_spec h
    · intro hxy
      exact Sum.inr.inj (M.unique (Classical.choose_spec h) hxy)
  · simp only [forwardOption, dif_neg h, reduceCtorEq, false_iff]
    exact fun hxy => h ⟨y, hxy⟩

theorem Matching.backwardOption_eq_some_iff (M : Matching (Sum X Y))
    (x : X) (y : Y) :
    M.backwardOption y = some x ↔ M.Rel (.inr y) (.inl x) := by
  classical
  by_cases h : ∃ z, M.Rel (.inr y) (.inl z)
  · simp only [backwardOption, dif_pos h, Option.some.injEq]
    constructor
    · intro hyx
      subst x
      exact Classical.choose_spec h
    · intro hyx
      exact Sum.inl.inj (M.unique (Classical.choose_spec h) hyx)
  · simp only [backwardOption, dif_neg h, reduceCtorEq, false_iff]
    exact fun hyx => h ⟨x, hyx⟩

/-- The two optional neighbour functions agree exactly on matched pairs. -/
theorem Matching.option_inverse_iff (M : Matching (Sum X Y))
    (x : X) (y : Y) :
    M.forwardOption x = some y ↔ M.backwardOption y = some x := by
  rw [M.forwardOption_eq_some_iff, M.backwardOption_eq_some_iff]
  exact ⟨M.symm, M.symm⟩

variable {V : Nat → Type u}

/-- All adjacent partial matchings form a layer-matching system. -/
noncomputable def layerMatchOfMatchings
    (M : ∀ n, Matching (Sum (V n) (V (n + 1)))) : LayerMatch V where
  forward n x := (M n).forwardOption x
  backward n y := (M n).backwardOption y
  inverse_iff n x y := (M n).option_inverse_iff x y

/-- Even after taking arbitrary transitive chains of the adjacent matchings,
one connected component cannot contain two different pieces in one block. -/
theorem layerMatching_no_merging
    (M : ∀ n, Matching (Sum (V n) (V (n + 1))))
    (n : Nat) (x y : V n)
    (h : (layerMatchOfMatchings M).Connected ⟨n, x⟩ ⟨n, y⟩) :
    x = y :=
  (layerMatchOfMatchings M).connected_same_layer n x y h

end GluingEPPA.Steiner.ChainValuation
