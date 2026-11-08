import GluingEPPA.BinaryOrbitSaturatedRelationalEPPA

/-!
# No involutive extension of the partial swap in the relational language

This is the negative counterpart of the all-size EPPA theorem in
BinaryOrbitSaturatedRelationalEPPA. It formulates the finite obstruction
in exactly the same \`RelStructure\` and \`Embedding\` vocabulary.

The theorem does not assume any distinguished representative colouring
of the witness beyond a six-colour pullback presentation. It applies to
every induced embedding of the canonical three-point input and to every
involutive relation automorphism extending its partial swap.

A coherent EPPA map would supply just such an automorphism, because
the partial swap has order two and groupoid coherence forces the chosen
extension of the corresponding partial identity to be the identity.
-/

namespace GluingEPPA.BinaryOrbitNoncoherence

universe u

/-- The three-vertex obstruction, using the standard relational API. -/
theorem no_relational_involutive_swap
    {V : Type u} (colour : V → Fin 6)
    (ι : Embedding (binaryStructure embedInput) (binaryStructure colour))
    (φ : V ≃ V)
    (hφ : ∀ {n : Nat} (r : BinaryLanguage n) (q : Fin n → V),
      (binaryStructure colour).rel r (fun j => φ (q j)) ↔
      (binaryStructure colour).rel r q)
    (hswap : φ (ι.toFun 0) = ι.toFun 1)
    (hsquare : φ (φ (ι.toFun 2)) = ι.toFun 2) :
    False := by
  have h_input (i j : Fin 3) :
      templateRel (colour (ι.toFun i)) (colour (ι.toFun j)) ↔
      inputRel i j := by
    let pair : Fin 2 → Fin 3 := fun t => if t = 0 then i else j
    have h := ι.rel_iff BinaryLanguage.edge pair
    simpa [binaryStructure, pair, inputRel] using h
  have h_trip :
      ∀ i j : Fin 3,
        templateRel
          (colour (triplePoint (ι.toFun 0) (ι.toFun 1) (ι.toFun 2) i))
          (colour (triplePoint (ι.toFun 0) (ι.toFun 1) (ι.toFun 2) j)) ↔
        inputRel i j := by
    intro i j
    have h := h_input i j
    fin_cases i <;> fin_cases j <;>
      simpa [triplePoint] using h
  have h_preserves (x y : V) :
      templateRel (colour x) (colour y) ↔
      templateRel (colour (φ x)) (colour (φ y)) := by
    let pair : Fin 2 → V := fun t => if t = 0 then x else y
    have h := hφ BinaryLanguage.edge pair
    simpa [binaryStructure, pair] using h.symm
  exact no_involution_on_any_induced_input colour φ
    (ι.toFun 0) (ι.toFun 1) (ι.toFun 2)
    h_trip hswap hsquare h_preserves

end GluingEPPA.BinaryOrbitNoncoherence
