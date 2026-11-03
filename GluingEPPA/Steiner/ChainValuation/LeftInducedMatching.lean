import GluingEPPA.Steiner.ChainValuation.MatchingComponentStep

/-!
# Lifting the last-block matching to the old chain components

In the chain-restriction induction, every old M-component meets the final
Cayley block in at most one M-coset. Thus the map sending a last-block coset
to its old-chain component is injective on the cosets under consideration.
A partial matching between last-block cosets and new-block cosets therefore
induces a partial matching between whole old-chain components and new cosets.

This isolates the key inductive use of the no-merging invariant.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {P : Type u} {Q : Type v} {C : Type w}

/-- Relabel the left vertices of a bipartite matching through an injection.
Components not in the image of the injection remain unmatched. -/
def Matching.relabelLeft (M : Matching (Sum P Q))
    (f : P → C) (hf : Function.Injective f) :
    Matching (Sum C Q) where
  Rel x y :=
    match x, y with
    | .inl c, .inr q =>
        ∃ p, f p = c ∧ M.Rel (.inl p) (.inr q)
    | .inr q, .inl c =>
        ∃ p, f p = c ∧ M.Rel (.inl p) (.inr q)
    | _, _ => False
  symm := by
    intro x y hxy
    cases x <;> cases y <;> exact hxy
  unique := by
    intro x y z hxy hxz
    cases x with
    | inl c =>
      cases y with
      | inl _ => cases hxy
      | inr q =>
        cases z with
        | inl _ => cases hxz
        | inr q' =>
          obtain ⟨p, hp, hpq⟩ := hxy
          obtain ⟨p', hp', hpq'⟩ := hxz
          have heq : p = p' := hf (hp.trans hp'.symm)
          subst p'
          exact congrArg Sum.inr (Sum.inr.inj (M.unique hpq hpq'))
    | inr q =>
      cases y with
      | inr _ => cases hxy
      | inl c =>
        cases z with
        | inr _ => cases hxz
        | inl c' =>
          obtain ⟨p, hp, hpq⟩ := hxy
          obtain ⟨p', hp', hpq'⟩ := hxz
          have heq : p = p' :=
            Sum.inl.inj (M.unique (M.symm hpq) (M.symm hpq'))
          subst p'
          exact congrArg Sum.inl (hp.symm.trans hp')

/-- The induced attachment is precisely the original one, with its
old restricted coset relabelled by the containing old component. -/
theorem Matching.relabelLeft_apply
    (M : Matching (Sum P Q))
    (f : P → C) (hf : Function.Injective f)
    (p : P) (q : Q) (h : M.Rel (.inl p) (.inr q)) :
    (M.relabelLeft f hf).Rel (.inl (f p)) (.inr q) := by
  exact ⟨p, rfl, h⟩

/-- Conversely, a matched old component has one actual last-block coset
and an attachment to the new block. -/
theorem Matching.relabelLeft_extract
    (M : Matching (Sum P Q))
    (f : P → C) (hf : Function.Injective f)
    (c : C) (q : Q)
    (h : (M.relabelLeft f hf).Rel (.inl c) (.inr q)) :
    ∃ p, f p = c ∧ M.Rel (.inl p) (.inr q) := h

end GluingEPPA.Steiner.ChainValuation
