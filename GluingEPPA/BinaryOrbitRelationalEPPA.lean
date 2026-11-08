import GluingEPPA.BinaryOrbitColourShift
import GluingEPPA.RelPartialAut

/-!
# One-relation EPPA through the standard relational interface

This module connects the six-colour pullback relation to the library's
RelStructure/RelPartialAut API. The general finite-input witness is the
uniformly padded Fin 6 × (A ⊕ A). Every relation-preserving partial
equivalence of the input has an automorphism extension, and the extension
realises precisely that partial equivalence as the whole overlap.

The finite noncoherence obstruction is proved separately in
BinaryOrbitSmallEPPA. The stronger transitive covering orbit on the
colour-saturated witness is not claimed in this module.
-/

namespace GluingEPPA.BinaryOrbitNoncoherence

universe u

/-- The language contains exactly one binary relation symbol. -/
inductive BinaryLanguage : Nat → Type
  | edge : BinaryLanguage 2

/-- The induced directed graph, with loops, from a six-colour labelling. -/
def binaryStructure {A : Type u} (colour : A → Fin 6) :
    RelStructure BinaryLanguage A where
  rel := fun {_} r q =>
    match r with
    | .edge => templateRel (colour (q 0)) (colour (q 1))

/-- The distinguished copy in the uniformly padded witness is induced. -/
def paddedEmbedding {A : Type u} (colour : A → Fin 6) :
    Embedding (binaryStructure colour)
      (binaryStructure (fun v : PaddedWitness A => v.1)) where
  toFun := paddedRoot colour
  injective := paddedRoot_injective colour
  rel_iff := by
    intro n r q
    cases r
    rfl

/-- Any RelPartialAut in the standard interface preserves and reflects
    the binary template on all pairs of mapped vertices, including
    repeated coordinates (loops) and reversed ordered pairs. -/
theorem pairwise_of_relPartialAut {A : Type u} (colour : A → Fin 6)
    (f : RelPartialAut (binaryStructure colour)) :
    ∀ x x' y y' : A,
      f.val x = some y → f.val x' = some y' →
      (templateRel (colour x) (colour x') ↔
       templateRel (colour y) (colour y')) := by
  intro x x' y y' hx hx'
  let src : Fin 2 → A := fun j => if j = 0 then x else x'
  let tgt : Fin 2 → A := fun j => if j = 0 then y else y'
  have hpoint : ∀ j : Fin 2, f.val (src j) = some (tgt j) := by
    intro j
    fin_cases j <;> simp [src, tgt, hx, hx']
  have h := f.property BinaryLanguage.edge src tgt hpoint
  simpa [binaryStructure, src, tgt] using h

/-- PEquiv partial bijections are injective wherever they are defined. -/
theorem injective_of_relPartialAut {A : Type u} (colour : A → Fin 6)
    (f : RelPartialAut (binaryStructure colour)) :
    ∀ x y z : A,
      f.val x = some z → f.val y = some z → x = y := by
  intro x y z hx hy
  have hx' := (f.val.eq_some_iff).mpr hx
  have hy' := (f.val.eq_some_iff).mpr hy
  exact Option.some.inj (hx'.symm.trans hy')

/-- Class-specific EPPA in the same form as finite_relational_eppa,
    strengthened to give *whole* exact overlaps for every map. -/
theorem finite_binary_eppa_exact_overlaps
    {A : Type u} [Finite A] (colour : A → Fin 6) :
    ∃ (B : Type u) (T : RelStructure BinaryLanguage B)
      (ι : Embedding (binaryStructure colour) T),
      Finite B ∧
      ∀ f : RelPartialAut (binaryStructure colour),
        ∃ φ : B ≃ B,
          (∀ {n : Nat} (r : BinaryLanguage n) (q : Fin n → B),
            T.rel r (fun j => φ (q j)) ↔ T.rel r q) ∧
          (∀ x y : A, (φ (ι.toFun x) = ι.toFun y ↔
                         f.val x = some y)) := by
  let B := PaddedWitness A
  let T : RelStructure BinaryLanguage B :=
    binaryStructure (fun v : B => v.1)
  let ι : Embedding (binaryStructure colour) T := paddedEmbedding colour
  refine ⟨B, T, ι, inferInstance, ?_⟩
  intro f
  obtain ⟨φ, hpres, hoverlap⟩ :=
    exists_exact_extension_of_partial_relation_map colour f.val
      (injective_of_relPartialAut colour f)
      (pairwise_of_relPartialAut colour f)
  refine ⟨φ, ?_, ?_⟩
  · intro n r q
    cases r
    change templateRel ((φ (q 0)).1) ((φ (q 1)).1) ↔
      templateRel ((q 0).1) ((q 1).1)
    exact hpres (q 0) (q 1)
  · intro x y
    exact hoverlap x y

end GluingEPPA.BinaryOrbitNoncoherence
