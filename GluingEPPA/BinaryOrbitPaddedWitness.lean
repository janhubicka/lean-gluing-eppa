import GluingEPPA.BinaryOrbitFiberPadding

/-!
# A uniform exact-overlap witness for any finite three-point-template blowup

The input is any finite type A, coloured in the six-colour palette,
together with a partial injective map p compatible with one shift k.
The output is a permutation of the padded witness
  Fin 6 × (A ⊕ A)
that extends p and has *exactly* the prescribed intersection with
the distinguished embedded copy.

The separate partial-isomorphism/shift correspondence turns this
into EPPA for the whole finite relational class.
-/

namespace GluingEPPA.BinaryOrbitNoncoherence

universe u

abbrev PaddedWitness (A : Type u) := Fin 6 × (A ⊕ A)

def paddedRoot {A : Type u} (colour : A → Fin 6) (a : A) :
    PaddedWitness A :=
  (colour a, Sum.inl a)

def paddedTarget {A : Type u} (colour : A → Fin 6)
    (k : Fin 4) (p : A → Option A) (a : A) : PaddedWitness A :=
  (shift6 k (colour a),
    match p a with
    | none => Sum.inr a
    | some b => Sum.inl b)

theorem paddedRoot_injective {A : Type u} (colour : A → Fin 6) :
    Function.Injective (paddedRoot colour) := by
  intro x y h
  have h' := congrArg Prod.snd h
  simpa [paddedRoot] using h'

theorem paddedTarget_injective {A : Type u}
    (colour : A → Fin 6) (k : Fin 4) (p : A → Option A)
    (hp : ∀ x y z, p x = some z → p y = some z → x = y) :
    Function.Injective (paddedTarget colour k p) := by
  intro x y h
  cases hx : p x with
  | none =>
    cases hy : p y with
    | none =>
      have h' := congrArg Prod.snd h
      simpa [paddedTarget, hx, hy] using h'
    | some z =>
      have h' := congrArg Prod.snd h
      simp [paddedTarget, hx, hy] at h'
  | some z =>
    cases hy : p y with
    | none =>
      have h' := congrArg Prod.snd h
      simp [paddedTarget, hx, hy] at h'
    | some w =>
      have h' := congrArg Prod.snd h
      have hzw : z = w := by
        simpa [paddedTarget, hx, hy] using h'
      exact hp x y z hx (by simpa [hzw] using hy)

/-- Complete a partial colour-shifting bijection, using one private
    second copy of every index. The resulting overlap is exact. -/
theorem exists_padded_exact_extension
    {A : Type u} [Finite A]
    (colour : A → Fin 6) (k : Fin 4)
    (p : A → Option A)
    (hp : ∀ x y z, p x = some z → p y = some z → x = y)
    (hcolour : ∀ x y, p x = some y →
      colour y = shift6 k (colour x)) :
    ∃ h : PaddedWitness A ≃ PaddedWitness A,
      (∀ v, (h v).1 = shift6 k v.1) ∧
      (∀ x y, (h (paddedRoot colour x) = paddedRoot colour y ↔
                    p x = some y)) := by
  classical
  let σ : Fin 6 ≃ Fin 6 :=
    Equiv.ofBijective (shift6 k) (shift6_bijective k)
  obtain ⟨h, hshift, hmatch⟩ :=
    exists_colour_shift_extension σ
      (paddedRoot colour) (paddedTarget colour k p)
      (paddedRoot_injective colour)
      (paddedTarget_injective colour k p hp)
      (by intro x; rfl)
  refine ⟨h, ?_, ?_⟩
  · intro v
    exact hshift v
  · intro x y
    rw [hmatch x]
    cases hx : p x with
    | none =>
      simp [paddedTarget, paddedRoot, hx]
    | some z =>
      have hcz : shift6 k (colour x) = colour z :=
        (hcolour x z hx).symm
      constructor
      · intro hxy
        have hz : z = y := by
          have hi := congrArg Prod.snd hxy
          simpa [paddedTarget, paddedRoot, hx] using hi
        simpa [hx, hz]
      · intro hxy
        have hz : z = y := by
          simpa [hx] using hxy
        subst y
        simp [paddedTarget, paddedRoot, hx, hcz]

end GluingEPPA.BinaryOrbitNoncoherence
