import GluingEPPA.BinaryOrbitNoncoherence

/-!
# Finite EPPA certificates for the three-point binary-orbit example

This module checks the six-point ordinary EPPA witness and the
eight-point exact-overlap witness. It deliberately does NOT claim
the generic balanced-fibre EPPA theorem for all finite inputs.

All proofs are closed finite reductions over Fin types and contain no
axioms, `sorry` or additional assumptions.
-/

namespace GluingEPPA.BinaryOrbitNoncoherence

/-- Embed the three-point input a0,a1,b0 into the palette template. -/
def embedInput (x : Fin 3) : Fin 6 :=
  if x = 0 then 0 else if x = 1 then 1 else 2

def inputRel (x y : Fin 3) : Prop :=
  templateRel (embedInput x) (embedInput y)

instance (x y : Fin 3) : Decidable (inputRel x y) := by
  unfold inputRel
  infer_instance

/-- A partial injective map of the three-vertex input, preserving
    and reflecting the relation on its domain. -/
def IsPartialAut (p : Fin 3 → Option (Fin 3)) : Prop :=
  (∀ x x' y, p x = some y → p x' = some y → x = x') ∧
  (∀ x x' y y',
    p x = some y → p x' = some y' →
    (inputRel x x' ↔ inputRel y y'))

instance (p : Fin 3 → Option (Fin 3)) : Decidable (IsPartialAut p) := by
  unfold IsPartialAut
  infer_instance

/-- Translate the short colour orbit modulo 2 and the regular orbit
    modulo 4. In particular shift6 0 is the identity. -/
def shift6 (k : Fin 4) (x : Fin 6) : Fin 6 :=
  if x.val < 2 then
    ⟨(x.val + k.val) % 2, by omega⟩
  else
    ⟨2 + ((x.val - 2 + k.val) % 4), by omega⟩

theorem shift6_bijective :
    ∀ k : Fin 4, Function.Bijective (shift6 k) := by
  decide

theorem shift6_preserves :
    ∀ k : Fin 4, ∀ x y : Fin 6,
      (templateRel (shift6 k x) (shift6 k y) ↔
       templateRel x y) := by
  decide

/-- Every partial automorphism of the three-point input is induced
    by one of the four palette shifts. This is an exhaustive proof. -/
theorem six_point_eppa_certificate :
    ∀ p : Fin 3 → Option (Fin 3),
      IsPartialAut p →
      ∃ k : Fin 4,
        ∀ x y : Fin 3, p x = some y →
          shift6 k (embedInput x) = embedInput y := by
  decide

/-- Colour the eight-point witness: two a0 vertices, two a1 vertices,
    and one vertex of each of the four b-colours. -/
def colour8 (x : Fin 8) : Fin 6 :=
  if x.val < 2 then 0
  else if x.val < 4 then 1
  else ⟨2 + (x.val - 4), by omega⟩

def root8 (x : Fin 3) : Fin 8 :=
  if x = 0 then 0 else if x = 1 then 2 else 4

theorem root8_colours (x : Fin 3) :
    colour8 (root8 x) = embedInput x := by
  fin_cases x <;> decide

def witness8Rel (x y : Fin 8) : Prop :=
  templateRel (colour8 x) (colour8 y)

instance (x y : Fin 8) : Decidable (witness8Rel x y) := by
  unfold witness8Rel
  infer_instance

/-- One of 16 permutations: a global shift plus independent
    toggles of the two twins in the short-colour fibres. -/
def shift8 (k : Fin 4) (s0 s1 : Bool) (x : Fin 8) : Fin 8 :=
  if x.val < 4 then
    let a := x.val / 2
    let twin := x.val % 2
    let toggle := if a = 0 then (if s0 then 1 else 0)
                              else (if s1 then 1 else 0)
    ⟨2 * ((a + k.val) % 2) + ((twin + toggle) % 2), by omega⟩
  else
    ⟨4 + ((x.val - 4 + k.val) % 4), by omega⟩

theorem shift8_bijective :
    ∀ k : Fin 4, ∀ s0 s1 : Bool,
      Function.Bijective (shift8 k s0 s1) := by
  decide

theorem shift8_preserves :
    ∀ k : Fin 4, ∀ s0 s1 : Bool, ∀ x y : Fin 8,
      (witness8Rel (shift8 k s0 s1 x) (shift8 k s0 s1 y) ↔
       witness8Rel x y) := by
  decide

/-- Every partial automorphism is the *whole* intersection of
    the input copy with one of its 16 translates in the witness.
    For every input x and input y, the translate hits root y
    precisely when p maps x to y. -/
theorem eight_point_exact_overlap_certificate :
    ∀ p : Fin 3 → Option (Fin 3),
      IsPartialAut p →
      ∃ k : Fin 4, ∃ s0 s1 : Bool,
        ∀ x y : Fin 3,
          ((shift8 k s0 s1 (root8 x) = root8 y) ↔
           p x = some y) := by
  decide

end GluingEPPA.BinaryOrbitNoncoherence
