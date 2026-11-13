import GluingEPPA.Steiner.ChainValuation.Matching

/-!
# From compatible block transitions to the global chain letter permutation

This isolates the only property needed from the chain quotient for a fixed
letter: whenever two block occurrences represent the same quotient vertex and
both blocks contain that letter, their next block occurrences represent the
same quotient vertex.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w
variable {I : Type u} {E : Type v}
variable {B : I → Type w} {X : Type w}

/-- The union of one labelled edge from every active block. -/
def blockEdgeRel
    (embed : ∀ i, B i → X)
    (active : I → E → Prop)
    (step : ∀ i, E → B i → B i)
    (e : E) (x y : X) : Prop :=
  ∃ i b, active i e ∧ embed i b = x ∧ embed i (step i e b) = y

/-- Compatible involutive block transitions form a matching on the quotient. -/
def blockMatching
    (embed : ∀ i, B i → X)
    (active : I → E → Prop)
    (step : ∀ i, E → B i → B i)
    (hinv : ∀ i e, active i e → Function.Involutive (step i e))
    (hcompat : ∀ i j e bi bj,
      active i e → active j e →
      embed i bi = embed j bj →
      embed i (step i e bi) = embed j (step j e bj))
    (e : E) : Matching X where
  Rel := blockEdgeRel embed active step e
  symm := by
    rintro x y ⟨i, b, he, rfl, rfl⟩
    refine ⟨i, step i e b, he, rfl, ?_⟩
    rw [hinv i e he b]
  unique := by
    rintro x y z ⟨i, bi, hei, hix, hiy⟩
      ⟨j, bj, hej, hjx, hjz⟩
    rw [← hiy, ← hjz]
    exact hcompat i j e bi bj hei hej (hix.trans hjx.symm)

/-- The completed global letter permutation follows every active block edge. -/
theorem blockMatching_perm_apply
    (embed : ∀ i, B i → X)
    (active : I → E → Prop)
    (step : ∀ i, E → B i → B i)
    (hinv : ∀ i e, active i e → Function.Involutive (step i e))
    (hcompat : ∀ i j e bi bj,
      active i e → active j e →
      embed i bi = embed j bj →
      embed i (step i e bi) = embed j (step j e bj))
    {i : I} {e : E} (he : active i e) (b : B i) :
    (blockMatching embed active step hinv hcompat e).perm (embed i b) =
      embed i (step i e b) := by
  apply Matching.perm_eq_of_rel
  exact ⟨i, b, he, rfl, rfl⟩

/-- Consequently every global chain letter is involutive. -/
theorem blockMatching_perm_involutive
    (embed : ∀ i, B i → X)
    (active : I → E → Prop)
    (step : ∀ i, E → B i → B i)
    (hinv : ∀ i e, active i e → Function.Involutive (step i e))
    (hcompat : ∀ i j e bi bj,
      active i e → active j e →
      embed i bi = embed j bj →
      embed i (step i e bi) = embed j (step j e bj))
    (e : E) :
    Function.Involutive (blockMatching embed active step hinv hcompat e).perm :=
  (blockMatching embed active step hinv hcompat e).next_involutive

end GluingEPPA.Steiner.ChainValuation
