import GluingEPPA.BinaryOrbitRelationalEPPA

/-!
# Colour-saturated exact-overlap witnesses

The uniform Fin 6 × (A ⊕ A) witness proves EPPA, but if the input
uses only one C4-orbit of colours, unused colour classes cannot be
covered by its orbit of canonical input copies.

Here the palette is restricted to the C4-saturation of the colours
actually present in A. Every nonempty colour class still has 2|A|
points, and the fibrewise matching theorem applies unchanged.

Two statements are separated:
* arbitrary finite partial maps have exact-overlap extensions;
* every point of the restricted witness lies in an automorphic copy
  of the original input.
-/

namespace GluingEPPA.BinaryOrbitNoncoherence

universe u

def addShift (k l : Fin 4) : Fin 4 :=
  ⟨(k.val + l.val) % 4, by omega⟩

def inverseShift (k : Fin 4) : Fin 4 :=
  ⟨(4 - k.val) % 4, by omega⟩

theorem shift6_comp : ∀ k l : Fin 4, ∀ x : Fin 6,
    shift6 (addShift k l) x = shift6 k (shift6 l x) := by
  decide

theorem shift6_inverse_left : ∀ k : Fin 4, ∀ x : Fin 6,
    shift6 (inverseShift k) (shift6 k x) = x := by
  decide

theorem shift6_inverse_right : ∀ k : Fin 4, ∀ x : Fin 6,
    shift6 k (shift6 (inverseShift k) x) = x := by
  decide

theorem shift6_zero : ∀ x : Fin 6, shift6 0 x = x := by
  decide

/-- Colours that occur somewhere in the C4 orbit of an input colour. -/
def ActiveColour {A : Type u} (colour : A → Fin 6) :=
  {c : Fin 6 // ∃ a : A, ∃ k : Fin 4, shift6 k (colour a) = c}

theorem active_shift_closed {A : Type u} (colour : A → Fin 6)
    (k : Fin 4) (c : Fin 6)
    (hc : ∃ a : A, ∃ t : Fin 4, shift6 t (colour a) = c) :
    ∃ a : A, ∃ t : Fin 4, shift6 t (colour a) = shift6 k c := by
  obtain ⟨a, t, ht⟩ := hc
  refine ⟨a, addShift k t, ?_⟩
  rw [shift6_comp, ht]

/-- The global colour shift restricts to a permutation of active colours. -/
def activeShift {A : Type u} (colour : A → Fin 6) (k : Fin 4) :
    ActiveColour colour ≃ ActiveColour colour where
  toFun x := ⟨shift6 k x.val, active_shift_closed colour k x.val x.property⟩
  invFun x := ⟨shift6 (inverseShift k) x.val,
    active_shift_closed colour (inverseShift k) x.val x.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact shift6_inverse_left k x.val
  right_inv := by
    intro x
    apply Subtype.ext
    exact shift6_inverse_right k x.val

abbrev ActiveWitness {A : Type u} (colour : A → Fin 6) :=
  ActiveColour colour × (A ⊕ A)

def activeRoot {A : Type u} (colour : A → Fin 6) (a : A) :
    ActiveWitness colour :=
  (⟨colour a, a, 0, shift6_zero (colour a)⟩, Sum.inl a)

def activeTarget {A : Type u} (colour : A → Fin 6)
    (k : Fin 4) (p : A → Option A) (a : A) :
    ActiveWitness colour :=
  (activeShift colour k (activeRoot colour a).1,
    match p a with
    | none => Sum.inr a
    | some b => Sum.inl b)

theorem activeRoot_injective {A : Type u} (colour : A → Fin 6) :
    Function.Injective (activeRoot colour) := by
  intro x y h
  have hs := congrArg Prod.snd h
  simpa [activeRoot] using hs

theorem activeTarget_injective {A : Type u}
    (colour : A → Fin 6) (k : Fin 4) (p : A → Option A)
    (hp : ∀ x y z, p x = some z → p y = some z → x = y) :
    Function.Injective (activeTarget colour k p) := by
  intro x y h
  have hh := congrArg (fun v : ActiveWitness colour => (v.1.val, v.2)) h
  have hpadded : paddedTarget colour k p x = paddedTarget colour k p y := by
    simpa [activeTarget, paddedTarget, activeRoot, activeShift] using hh
  exact paddedTarget_injective colour k p hp hpadded

/-- Exact partial-map extension on the restricted, colour-saturated witness. -/
theorem exists_active_exact_extension
    {A : Type u} [Finite A] (colour : A → Fin 6)
    (k : Fin 4) (p : A → Option A)
    (hinj : ∀ x y z, p x = some z → p y = some z → x = y)
    (hcolour : ∀ x y, p x = some y →
      colour y = shift6 k (colour x)) :
    ∃ h : ActiveWitness colour ≃ ActiveWitness colour,
      (∀ v w, templateRel (h v).1.val (h w).1.val ↔
                templateRel v.1.val w.1.val) ∧
      (∀ x y, (h (activeRoot colour x) = activeRoot colour y ↔
                p x = some y)) := by
  classical
  obtain ⟨h, hshift, hmatch⟩ :=
    exists_colour_shift_extension (activeShift colour k)
      (activeRoot colour) (activeTarget colour k p)
      (activeRoot_injective colour)
      (activeTarget_injective colour k p hinj)
      (by intro x; rfl)
  refine ⟨h, ?_, ?_⟩
  · intro v w
    have hv : (h v).1.val = shift6 k v.1.val := by
      simpa [activeShift] using congrArg Subtype.val (hshift v)
    have hw : (h w).1.val = shift6 k w.1.val := by
      simpa [activeShift] using congrArg Subtype.val (hshift w)
    rw [hv, hw]
    exact shift6_preserves k v.1.val w.1.val
  · intro x y
    rw [hmatch x]
    cases hx : p x with
    | none =>
      simp [activeTarget, activeRoot, hx]
    | some z =>
      constructor
      · intro hxy
        have hs := congrArg Prod.snd hxy
        have hz : z = y := by
          simpa [activeTarget, activeRoot, hx] using hs
        simpa [hx, hz]
      · intro hxy
        have hz : z = y := by simpa [hx] using hxy
        subst y
        apply Prod.ext
        · apply Subtype.ext
          exact (hcolour x z hx).symm
        · simp [activeTarget, activeRoot, hx]

/-- The active witness is covered by the automorphism orbit of the root copy. -/
theorem active_orbit_covers
    {A : Type u} [Finite A] (colour : A → Fin 6) :
    ∀ v : ActiveWitness colour,
      ∃ (a : A) (h : ActiveWitness colour ≃ ActiveWitness colour),
        (∀ x y, templateRel (h x).1.val (h y).1.val ↔
                  templateRel x.1.val y.1.val) ∧
        h (activeRoot colour a) = v := by
  classical
  intro v
  obtain ⟨a, k, hc⟩ := v.1.property
  let src : PUnit → ActiveWitness colour := fun _ => activeRoot colour a
  let tgt : PUnit → ActiveWitness colour := fun _ => v
  have src_inj : Function.Injective src := by
    intro x y _
    exact Subsingleton.elim x y
  have tgt_inj : Function.Injective tgt := by
    intro x y _
    exact Subsingleton.elim x y
  have hcol : ∀ d, (tgt d).1 = activeShift colour k (src d).1 := by
    intro d
    apply Subtype.ext
    exact hc.symm
  obtain ⟨h, hshift, hhit⟩ :=
    exists_colour_shift_extension (activeShift colour k)
      src tgt src_inj tgt_inj hcol
  refine ⟨a, h, ?_, ?_⟩
  · intro x y
    have hx := congrArg Subtype.val (hshift x)
    have hy := congrArg Subtype.val (hshift y)
    change (h x).1.val = shift6 k x.1.val at hx
    change (h y).1.val = shift6 k y.1.val at hy
    rw [hx, hy]
    exact shift6_preserves k x.1.val y.1.val
  · simpa [src, tgt] using hhit PUnit.unit

end GluingEPPA.BinaryOrbitNoncoherence
