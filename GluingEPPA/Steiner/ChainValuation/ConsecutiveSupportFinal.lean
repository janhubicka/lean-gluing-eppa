import GluingEPPA.Steiner.ChainValuation.ConsecutiveHistoricalSupport

/-!
# An interval reaching the final block is an active suffix

The support-interval argument must not silently assume the
active-suffix condition. This file derives it from two facts:
(1) the support is a consecutive interval, and
(2) its final historical index is active.

The proof works for lists of propositions and does not require
decidable support predicates, finite enumeration, or a fabricated
global group. This is the combinatorial bridge between the
historical last-block witness and the explicit hypothesis in
historicalSupport_extend_consecutive.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u
variable {α : Type u}

/-- Every nonempty finite list has a final element and a prefix. -/
private theorem exists_snoc :
    ∀ (xs : List α), xs ≠ [] →
      ∃ prefix : List α, ∃ last : α, xs = prefix ++ [last] := by
  intro xs
  induction xs with
  | nil =>
    intro hne
    exact False.elim (hne rfl)
  | cons a xs ih =>
    intro _
    by_cases hempty : xs = []
    · subst xs
      exact ⟨[], a, rfl⟩
    · obtain ⟨prefix, last, hlast⟩ := ih hempty
      refine ⟨a :: prefix, last, ?_⟩
      simp [hlast]

/-- Equality of two lists written with a singleton final element
forces equality of those final elements, regardless of prefix lengths. -/
private theorem append_singleton_last_eq
    (xs ys : List α) (x y : α)
    (h : xs ++ [x] = ys ++ [y]) : x = y := by
  have hrev : x :: xs.reverse = y :: ys.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse h
  exact (List.cons.inj hrev).1

/-- When the last historical support bit is true and all active
bits form one interval, no inactive suffix can remain. Thus the
support is a prefix of inactive blocks followed by an active suffix. -/
theorem consecutive_activeSuffix_of_last
    (xs : List Prop) (P : Prop)
    (hinterval : IsConsecutiveSupport (xs ++ [P]))
    (hP : P) :
    IsActiveSuffixSupport (xs ++ [P]) := by
  obtain ⟨pre, active, post, hlist, hpre, hactive, hpost⟩ := hinterval
  by_cases hempty : post = []
  · subst post
    refine ⟨pre, active, ?_, hpre, hactive⟩
    simpa using hlist
  · obtain ⟨front, last, hsnoc⟩ := exists_snoc post hempty
    have hend : xs ++ [P] = (pre ++ active ++ front) ++ [last] := by
      calc
        xs ++ [P] = pre ++ active ++ post := hlist
        _ = (pre ++ active ++ front) ++ [last] := by
          rw [hsnoc]
          simp [List.append_assoc]
    have hEq : P = last :=
      append_singleton_last_eq xs (pre ++ active ++ front) P last hend
    have hmem : last ∈ post := by rw [hsnoc]; simp
    exact False.elim ((hpost last hmem) (hEq ▸ hP))

/-- Therefore a single verified last-index witness is sufficient
to discharge the active-suffix obligation in the geometric
consecutive-support step. -/
theorem consecutive_append_of_last_witness
    (xs : List Prop) (P Q : Prop)
    (hinterval : IsConsecutiveSupport (xs ++ [Q]))
    (hQ : Q) :
    IsConsecutiveSupport ((xs ++ [Q]) ++ [P]) := by
  apply consecutive_append_of_interface
    (xs ++ [Q]) P hinterval
  intro _
  exact consecutive_activeSuffix_of_last xs Q hinterval hQ

end GluingEPPA.Steiner.ChainValuation
