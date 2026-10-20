import Mathlib

/-!
# Lifting maps on involutive generators

A map on generators that respects every identity word extends to a group
homomorphism. The proof uses positive words because the source generators
are involutions. No presentation or quotient existence theorem is assumed.
-/

namespace GluingEPPA.Steiner

universe u v w
variable {E : Type u} {G : Type v} {H : Type w} [Group G] [Group H]

def wordValue (a : E → G) (w : List E) : G := (w.map a).prod

@[simp] theorem wordValue_nil (a : E → G) : wordValue a [] = 1 := rfl

@[simp] theorem wordValue_cons (a : E → G) (e : E) (w : List E) :
    wordValue a (e :: w) = a e * wordValue a w := rfl

@[simp] theorem wordValue_singleton (a : E → G) (e : E) :
    wordValue a [e] = a e := by simp [wordValue]

@[simp] theorem wordValue_append (a : E → G) (w v : List E) :
    wordValue a (w ++ v) = wordValue a w * wordValue a v := by
  simp [wordValue, List.prod_append]

theorem involutive_inv_eq {g : G} (h : g * g = 1) : g⁻¹ = g := by
  calc
    g⁻¹ = g⁻¹ * 1 := (mul_one _).symm
    _ = g⁻¹ * (g * g) := by rw [h]
    _ = g := by group

theorem wordValue_reverse (a : E → G) (ha : ∀ e, a e * a e = 1)
    (w : List E) : wordValue a w.reverse = (wordValue a w)⁻¹ := by
  induction w with
  | nil => simp
  | cons e w ih =>
      simp only [List.reverse_cons, wordValue_append, wordValue_singleton,
        wordValue_cons, mul_inv_rev, ih, involutive_inv_eq (ha e)]

/-- Source-equal words have target-equal values. Two identity words with the
same reversed suffix suffice; target generators need not be assumed involutive. -/
theorem wordValue_eq_of_relations (a : E → G) (b : E → H)
    (ha : ∀ e, a e * a e = 1)
    (hrel : ∀ w, wordValue a w = 1 → wordValue b w = 1)
    (u v : List E) (h : wordValue a u = wordValue a v) :
    wordValue b u = wordValue b v := by
  have hu : wordValue a (u ++ v.reverse) = 1 := by
    rw [wordValue_append, wordValue_reverse a ha, h, mul_inv_cancel]
  have hv : wordValue a (v ++ v.reverse) = 1 := by
    rw [wordValue_append, wordValue_reverse a ha, mul_inv_cancel]
  have hbu := hrel (u ++ v.reverse) hu
  have hbv := hrel (v ++ v.reverse) hv
  rw [wordValue_append] at hbu hbv
  exact mul_right_cancel (hbu.trans hbv.symm)

/-- The subgroup of positive word values is a group for involutive generators. -/
def wordSubgroup (a : E → G) (ha : ∀ e, a e * a e = 1) : Subgroup G where
  carrier := {g | ∃ w, wordValue a w = g}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro g h ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u ++ v, wordValue_append a u v⟩
  inv_mem' := by
    rintro g ⟨w, rfl⟩
    exact ⟨w.reverse, wordValue_reverse a ha w⟩

theorem exists_word_of_closure (a : E → G) (ha : ∀ e, a e * a e = 1)
    (hgen : Subgroup.closure (Set.range a) = ⊤) (g : G) :
    ∃ w, wordValue a w = g := by
  have hle : Subgroup.closure (Set.range a) ≤ wordSubgroup a ha := by
    apply Subgroup.closure_le.mpr
    rintro x ⟨e, rfl⟩
    exact ⟨[e], wordValue_singleton a e⟩
  apply hle
  rw [hgen]
  trivial

noncomputable def representativeWord (a : E → G)
    (hgen : ∀ g, ∃ w, wordValue a w = g) (g : G) : List E :=
  Classical.choose (hgen g)

@[simp] theorem representativeWord_value (a : E → G)
    (hgen : ∀ g, ∃ w, wordValue a w = g) (g : G) :
    wordValue a (representativeWord a hgen g) = g :=
  Classical.choose_spec (hgen g)

noncomputable def involutiveWordLift (a : E → G) (b : E → H)
    (ha : ∀ e, a e * a e = 1)
    (hgen : ∀ g, ∃ w, wordValue a w = g)
    (hrel : ∀ w, wordValue a w = 1 → wordValue b w = 1) : G →* H where
  toFun g := wordValue b (representativeWord a hgen g)
  map_one' := hrel _ (representativeWord_value a hgen 1)
  map_mul' g h := by
    calc
      wordValue b (representativeWord a hgen (g * h)) =
          wordValue b (representativeWord a hgen g ++ representativeWord a hgen h) := by
        apply wordValue_eq_of_relations a b ha hrel
        simp
      _ = wordValue b (representativeWord a hgen g) *
          wordValue b (representativeWord a hgen h) := wordValue_append b _ _

theorem involutiveWordLift_word (a : E → G) (b : E → H)
    (ha : ∀ e, a e * a e = 1)
    (hgen : ∀ g, ∃ w, wordValue a w = g)
    (hrel : ∀ w, wordValue a w = 1 → wordValue b w = 1) (w : List E) :
    involutiveWordLift a b ha hgen hrel (wordValue a w) = wordValue b w := by
  change wordValue b (representativeWord a hgen (wordValue a w)) = wordValue b w
  apply wordValue_eq_of_relations a b ha hrel
  exact representativeWord_value a hgen _

theorem involutiveWordLift_generator (a : E → G) (b : E → H)
    (ha : ∀ e, a e * a e = 1)
    (hgen : ∀ g, ∃ w, wordValue a w = g)
    (hrel : ∀ w, wordValue a w = 1 → wordValue b w = 1) (e : E) :
    involutiveWordLift a b ha hgen hrel (a e) = b e := by
  simpa only [wordValue_singleton] using
    involutiveWordLift_word a b ha hgen hrel [e]

end GluingEPPA.Steiner
