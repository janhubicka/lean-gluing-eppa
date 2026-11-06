import Mathlib

/-!
# A six-colour template obstructing coherent EPPA

This module isolates the finite obstruction from
`janhubicka/Otto-simplified/eppa_without_coherent_eppa.tex`.
The palette has colours a0,a1,b0,b1,b2,b3, encoded by Fin 6.
Only the relation-preservation and involution contradiction is
formalized here. The positive EPPA theorem and the statement about
all structures in the Fraïssé class are separate tasks.
-/

namespace GluingEPPA.BinaryOrbitNoncoherence

/-- The single directed binary relation on the six-colour template.
    Indices 0,1 are a0,a1; indices 2,3,4,5 are b0,b1,b2,b3.
    The b-colours have loops; the a-colours do not. -/
def templateRel (x y : Fin 6) : Prop :=
  (x = 0 ∧ y = 1) ∨
  (x = 1 ∧ y = 0) ∨
  (x = 0 ∧ (y = 2 ∨ y = 4)) ∨
  (x = 1 ∧ (y = 3 ∨ y = 5)) ∨
  (x = 2 ∧ (y = 2 ∨ y = 3)) ∨
  (x = 3 ∧ (y = 3 ∨ y = 4)) ∨
  (x = 4 ∧ (y = 4 ∨ y = 5)) ∨
  (x = 5 ∧ (y = 5 ∨ y = 2))

/-- A b-colour y that has a loop and receives an arrow from a1
    cannot have its edge with b0 symmetric. This is a finite
    decidable truth-table certificate, with six possible values of y. -/
theorem template_forbidden_pair :
    ∀ y : Fin 6,
      templateRel y y →
      templateRel (1 : Fin 6) y →
      (templateRel (2 : Fin 6) y ↔ templateRel y (2 : Fin 6)) →
      False := by
  decide

/-- The noncoherence obstruction is universal in the size of a
    putative witness. The witness may be infinite, and h need
    not be injective or surjective: preserving the relation,
    exchanging the two a-points, and squaring to the identity
    on z already yields a contradiction. -/
theorem no_involutive_extension
    {V : Type*} (colour : V → Fin 6) (h : V → V)
    (x0 x1 z : V)
    (hx0_colour : colour x0 = 0)
    (hx1_colour : colour x1 = 1)
    (hz_colour : colour z = 2)
    (hx0_swap : h x0 = x1)
    (h_square_z : h (h z) = z)
    (h_preserves : ∀ x y : V,
      templateRel (colour x) (colour y) ↔
      templateRel (colour (h x)) (colour (h y))) :
    False := by
  have hz_loop : templateRel (colour z) (colour z) := by
    rw [hz_colour]
    decide
  have hy_loop : templateRel (colour (h z)) (colour (h z)) :=
    (h_preserves z z).mp hz_loop
  have original_arrow : templateRel (colour x0) (colour z) := by
    rw [hx0_colour, hz_colour]
    decide
  have shifted_arrow : templateRel (1 : Fin 6) (colour (h z)) := by
    simpa [hx0_swap, hx1_colour] using
      ((h_preserves x0 z).mp original_arrow)
  have reverse_equivalence :
      templateRel (2 : Fin 6) (colour (h z)) ↔
      templateRel (colour (h z)) (2 : Fin 6) := by
    simpa [h_square_z, hz_colour] using (h_preserves z (h z))
  exact template_forbidden_pair (colour (h z))
    hy_loop shifted_arrow reverse_equivalence

end GluingEPPA.BinaryOrbitNoncoherence
