import GluingEPPA.Steiner.ChainValuation.MatchingComponents

/-!
# One-step component classification along a partial matching

At a new chain attachment, old restricted components and new Cayley coset
pieces form a partial matching. Every resulting component therefore contains
exactly one old component, with at most one new piece attached, or consists
of a new piece which had no old neighbour.

This is the combinatorial induction step used in the chain-restriction
argument. It is not yet the theorem identifying M-connectivity of the
full Cayley chain with these coset-piece components.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {X : Type u} {Y : Type v}

/-- Every matching component either has an old-layer representative or is
an unmatched vertex of the newly attached layer. -/
theorem Matching.component_old_or_unmatched_new
    (M : Matching (Sum X Y)) (q : Quotient M.componentSetoid) :
    (∃ x : X, Quotient.mk M.componentSetoid (Sum.inl x) = q) ∨
      (∃ y : Y, Quotient.mk M.componentSetoid (Sum.inr y) = q ∧
        ∀ x : X, ¬ M.Rel (Sum.inl x) (Sum.inr y)) := by
  refine Quotient.inductionOn q ?_
  intro z
  cases z with
  | inl x =>
    exact Or.inl ⟨x, rfl⟩
  | inr y =>
    by_cases h : ∃ x : X, M.Rel (Sum.inl x) (Sum.inr y)
    · obtain ⟨x, hxy⟩ := h
      exact Or.inl ⟨x, Quotient.sound (Or.inr hxy)⟩
    · exact Or.inr ⟨y, rfl, fun x hx => h ⟨x, hx⟩⟩

/-- A matched new piece is in the component of exactly one old piece,
provided the matching has no edges within the old layer. -/
theorem Matching.old_component_unique_of_match
    (M : Matching (Sum X Y))
    (hno : ∀ x x' : X, ¬ M.Rel (Sum.inl x) (Sum.inl x'))
    {x x' : X} {y : Y}
    (hx : M.Rel (Sum.inl x) (Sum.inr y))
    (hx' : M.Rel (Sum.inl x') (Sum.inr y)) : x = x' := by
  have h := M.unique (M.symm hx) (M.symm hx')
  exact Sum.inl.inj h

/-- Likewise every old piece can acquire at most one new piece. -/
theorem Matching.new_component_unique_of_match
    (M : Matching (Sum X Y))
    {x : X} {y y' : Y}
    (hy : M.Rel (Sum.inl x) (Sum.inr y))
    (hy' : M.Rel (Sum.inl x) (Sum.inr y')) : y = y' := by
  exact Sum.inr.inj (M.unique hy hy')

/-- The quotient component of an unmatched new piece has no old
representative. -/
theorem Matching.unmatched_new_not_old
    (M : Matching (Sum X Y))
    {y : Y} (hy : ∀ x : X, ¬ M.Rel (Sum.inl x) (Sum.inr y))
    (x : X) :
    Quotient.mk M.componentSetoid (Sum.inr y) ≠
      Quotient.mk M.componentSetoid (Sum.inl x) := by
  intro h
  rcases (M.quotient_eq_iff (Sum.inr y) (Sum.inl x)).mp h with hEq | hEdge
  · cases hEq
  · exact hy x (M.symm hEdge)

end GluingEPPA.Steiner.ChainValuation
