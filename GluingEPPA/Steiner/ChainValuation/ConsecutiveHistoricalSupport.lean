import GluingEPPA.Steiner.ChainValuation.HistoricalSupportTransport

/-!
# Consecutive support invariant for finite separated chains

The geometric support transition theorem says that an old component's
ordered support changes from l to l ++ [P], where P is exactly the
proposition that it meets the new attaching interface.

This module isolates the remaining finite-list combinatorics:
- appending a false bit preserves a consecutive support;
- appending a true bit preserves one whose active part reaches the
  old final block;
- a newly born component has an inactive prefix followed by one
  active final block.

No gap-filling or interval conclusion is assumed. The last theorem
applies this combinatorial argument directly to the actual
historical-support transition, making the remaining active-suffix
condition an explicit hypothesis instead of hiding it in prose.
-/

namespace GluingEPPA.Steiner.ChainValuation

/-- Every truth value in the given list is false. -/
def AllInactive (l : List Prop) : Prop :=
  ∀ p : Prop, p ∈ l → ¬ p

/-- Every truth value in the given list is true. -/
def AllActive (l : List Prop) : Prop :=
  ∀ p : Prop, p ∈ l → p

/-- The active historical blocks form a (possibly empty) consecutive
interval, with inactive blocks before and after. -/
def IsConsecutiveSupport (l : List Prop) : Prop :=
  ∃ pre active post : List Prop,
    l = pre ++ active ++ post ∧
    AllInactive pre ∧ AllActive active ∧ AllInactive post

/-- The active part is a suffix: no inactive block follows it.
This is the additional invariant needed when the component meets
the last block of the old chain. -/
def IsActiveSuffixSupport (l : List Prop) : Prop :=
  ∃ pre active : List Prop,
    l = pre ++ active ∧ AllInactive pre ∧ AllActive active

theorem activeSuffix_isConsecutive (l : List Prop)
    (h : IsActiveSuffixSupport l) : IsConsecutiveSupport l := by
  obtain ⟨pre, active, hl, hpre, hactive⟩ := h
  refine ⟨pre, active, [], ?_, hpre, hactive, ?_⟩
  · simpa using hl
  · intro p hp
    simp at hp

/-- A component which does not meet the new block simply acquires
one additional inactive historical index. -/
theorem consecutive_append_inactive (l : List Prop)
    (h : IsConsecutiveSupport l) :
    IsConsecutiveSupport (l ++ [False]) := by
  obtain ⟨pre, active, post, hl, hpre, hactive, hpost⟩ := h
  refine ⟨pre, active, post ++ [False], ?_, hpre, hactive, ?_⟩
  · simp only [hl, List.append_assoc]
  · intro p hp
    rcases List.mem_append.mp hp with hmem | hmem
    · exact hpost p hmem
    · have heq : p = False := by simpa using hmem
      subst p
      exact (fun h => h)

/-- Appending the matched new block to an active suffix continues
that suffix by one active index. -/
theorem activeSuffix_append_active (l : List Prop)
    (h : IsActiveSuffixSupport l) :
    IsActiveSuffixSupport (l ++ [True]) := by
  obtain ⟨pre, active, hl, hpre, hactive⟩ := h
  refine ⟨pre, active ++ [True], ?_, hpre, ?_⟩
  · simp only [hl, List.append_assoc]
  · intro p hp
    rcases List.mem_append.mp hp with hmem | hmem
    · exact hactive p hmem
    · have heq : p = True := by simpa using hmem
      subst p
      trivial

/-- A new component consists of an inactive historical prefix and
the single new active block. -/
theorem inactivePrefix_append_active (pre : List Prop)
    (h : AllInactive pre) :
    IsActiveSuffixSupport (pre ++ [True]) := by
  refine ⟨pre, [True], rfl, h, ?_⟩
  intro p hp
  have heq : p = True := by simpa using hp
  subst p
  trivial

/-- The exact two-way induction split for appending one new block.
When P holds we need an active old suffix; otherwise the old
component remains unchanged except for a false final bit. -/
theorem consecutive_append_of_interface
    (l : List Prop) (P : Prop)
    (hconsecutive : IsConsecutiveSupport l)
    (hsuffix : P → IsActiveSuffixSupport l) :
    IsConsecutiveSupport (l ++ [P]) := by
  classical
  by_cases hp : P
  · simpa [hp] using activeSuffix_isConsecutive
      (l ++ [True]) (activeSuffix_append_active l (hsuffix hp))
  · simpa [hp] using consecutive_append_inactive l hconsecutive

end GluingEPPA.Steiner.ChainValuation
