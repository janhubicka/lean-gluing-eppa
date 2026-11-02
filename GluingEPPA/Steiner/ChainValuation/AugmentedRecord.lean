import GluingEPPA.Steiner.RecursiveRecord

/-!
# Adding finite permutation tests to one recursive valuation step

This is the exact operation used by the chain-augmented appendix: retain the
old literal record and append finitely many permutation coordinates. The new
group is the image of allowed words in the augmented record. No inclusion,
endpoint repair, or acyclicity property is assumed here.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace AugmentedRecord

attribute [local instance] Classical.propDecidable

universe u v w z q
variable {V : Type u} {E : Type v} {I : Type z} {J : Type q}
variable (D : EdgeGraph V E) (T : I → Set E) (K : I → Type w)
variable [∀ i, Group (K i)]
variable (a : ∀ i, E → K i) (ha : ∀ i e, e ∈ T i → a i e * a i e = 1)
variable (X : J → Type q) (τ : ∀ j, E → Equiv.Perm (X j))
variable (hτ : ∀ j e, τ j e * τ j e = 1)

/-- The old record together with all added finite permutation tests. -/
abbrev Product :=
  DirectRecord.Product D T K a ha × ∀ j, (Equiv.Perm (X j))ᵐᵒᵖ

noncomputable def testValue (w : List E) : ∀ j, (Equiv.Perm (X j))ᵐᵒᵖ :=
  fun j => (w.map (fun e => MulOpposite.op (τ j e))).prod

noncomputable def value (w : List E) : Product D T K a ha X :=
  (DirectRecord.value D T K a ha w, testValue X τ w)

noncomputable def letter (e : E) : Product D T K a ha X :=
  (DirectRecord.letter D T K a ha e, fun j => MulOpposite.op (τ j e))

@[simp] theorem value_nil :
    value D T K a ha X τ [] = 1 := by
  apply Prod.ext
  · exact DirectRecord.value_nil D T K a ha
  · funext j
    rfl

theorem value_cons (e : E) (w : List E) :
    value D T K a ha X τ (e :: w) =
      letter D T K a ha X τ e * value D T K a ha X τ w := by
  apply Prod.ext
  · exact DirectRecord.value_cons D T K a ha e w
  · funext j
    rfl

theorem value_append (p q : List E) :
    value D T K a ha X τ (p ++ q) =
      value D T K a ha X τ p * value D T K a ha X τ q := by
  induction p with
  | nil => simp only [List.nil_append, value_nil, one_mul]
  | cons e p ih => simp only [List.cons_append, value_cons, ih, mul_assoc]

theorem letter_involutive (e : E) :
    letter D T K a ha X τ e * letter D T K a ha X τ e = 1 := by
  apply Prod.ext
  · exact DirectRecord.letter_involutive D T K a ha e
  · funext j
    apply MulOpposite.unop_injective
    simpa using hτ j e

theorem letter_inv (e : E) :
    (letter D T K a ha X τ e)⁻¹ = letter D T K a ha X τ e := by
  have h := letter_involutive D T K a ha X τ hτ e
  calc
    (letter D T K a ha X τ e)⁻¹ =
        (letter D T K a ha X τ e)⁻¹ * 1 := (mul_one _).symm
    _ = (letter D T K a ha X τ e)⁻¹ *
        (letter D T K a ha X τ e * letter D T K a ha X τ e) := by rw [h]
    _ = letter D T K a ha X τ e := by group

theorem value_reverse (w : List E) :
    value D T K a ha X τ w.reverse =
      (value D T K a ha X τ w)⁻¹ := by
  induction w with
  | nil => simp only [List.reverse_nil, value_nil, inv_one]
  | cons e w ih =>
      simp only [List.reverse_cons, value_append, value_cons, value_nil,
        mul_one, ih, mul_inv_rev, letter_inv D T K a ha X τ hτ]

/-- The new finite group is literally the image of the augmented word record. -/
noncomputable def imageGroup (S : Set E) :
    Subgroup (Product D T K a ha X) where
  carrier := {g | ∃ w, (∀ e ∈ w, e ∈ S) ∧ value D T K a ha X τ w = g}
  one_mem' := ⟨[], by simp, value_nil D T K a ha X τ⟩
  mul_mem' := by
    rintro g h ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    refine ⟨p ++ q, ?_, value_append D T K a ha X τ p q⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hp e he
    · exact hq e he
  inv_mem' := by
    rintro g ⟨w, hw, rfl⟩
    refine ⟨w.reverse, ?_, value_reverse D T K a ha X τ hτ w⟩
    intro e he
    exact hw e (by simpa using he)

instance finiteImageGroup [Finite I] [Finite J] [Finite V]
    [∀ i, Finite (K i)] [∀ j, Finite (X j)] (S : Set E) :
    Finite (imageGroup D T K a ha X τ S) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype J := Fintype.ofFinite J
  letI : ∀ i, Fintype (K i) := fun i => Fintype.ofFinite (K i)
  letI : ∀ j, Fintype (X j) := fun j => Fintype.ofFinite (X j)
  letI : ∀ i, Fintype (D.Component (T i) (a i) (ha i)) :=
    fun i => Fintype.ofFinite (D.Component (T i) (a i) (ha i))
  letI : Fintype (DirectRecord.Product D T K a ha) := by
    unfold DirectRecord.Product
    infer_instance
  letI : ∀ j, Fintype ((Equiv.Perm (X j))ᵐᵒᵖ) :=
    fun j => Fintype.ofEquiv (Equiv.Perm (X j)) MulOpposite.opEquiv
  letI : Fintype (Product D T K a ha X) := by
    unfold Product
    infer_instance
  exact Finite.of_injective
    (fun g : imageGroup D T K a ha X τ S => (g.val : Product D T K a ha X))
    Subtype.val_injective

noncomputable def valuation (S : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) :
    imageGroup D T K a ha X τ S :=
  ⟨value D T K a ha X τ w, ⟨w, hw, rfl⟩⟩

noncomputable def generator (S : Set E) (e : E) (he : e ∈ S) :
    imageGroup D T K a ha X τ S :=
  ⟨letter D T K a ha X τ e, ⟨[e], by
    intro f hf
    have hfe : f = e := by simpa only [List.mem_singleton] using hf
    simpa only [hfe] using he, by
    simp only [value_cons, value_nil, mul_one]⟩⟩

theorem generator_involutive (S : Set E) (e : E) (he : e ∈ S) :
    generator D T K a ha X τ S e he *
      generator D T K a ha X τ S e he = 1 := by
  apply Subtype.ext
  exact letter_involutive D T K a ha X τ hτ e

/-- Extend the named generators by the identity outside the current alphabet. -/
noncomputable def totalGenerator (S : Set E) (e : E) :
    imageGroup D T K a ha X τ S :=
  if he : e ∈ S then generator D T K a ha X τ S e he else 1

theorem totalGenerator_mem (S : Set E) (e : E) (he : e ∈ S) :
    totalGenerator D T K a ha X τ S e =
      generator D T K a ha X τ S e he := by
  simp only [totalGenerator, dif_pos he]

theorem totalGenerator_not_mem (S : Set E) (e : E) (he : e ∉ S) :
    totalGenerator D T K a ha X τ S e = 1 := by
  simp only [totalGenerator, dif_neg he]

theorem totalGenerator_square (S : Set E) (e : E) :
    totalGenerator D T K a ha X τ S e *
      totalGenerator D T K a ha X τ S e = 1 := by
  by_cases he : e ∈ S
  · rw [totalGenerator_mem D T K a ha X τ S e he]
    exact generator_involutive D T K a ha X τ hτ S e he
  · rw [totalGenerator_not_mem D T K a ha X τ S e he, one_mul]

/-- Evaluation of an allowed word is its literal augmented record. -/
theorem totalGenerator_product (S : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) :
    ((w.map (totalGenerator D T K a ha X τ S)).prod).val =
      value D T K a ha X τ w := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      have he : e ∈ S := hw e (by simp)
      have hw' : ∀ f ∈ w, f ∈ S :=
        fun f hf => hw f (by simp [hf])
      change (totalGenerator D T K a ha X τ S e).val *
        ((w.map (totalGenerator D T K a ha X τ S)).prod).val =
          value D T K a ha X τ (e :: w)
      rw [totalGenerator_mem D T K a ha X τ S e he]
      change letter D T K a ha X τ e *
        ((w.map (totalGenerator D T K a ha X τ S)).prod).val =
          value D T K a ha X τ (e :: w)
      rw [ih hw', value_cons]

/-- Every augmented-record element is generated by the allowed named edges. -/
theorem image_generated (S : Set E)
    (g : imageGroup D T K a ha X τ S) :
    ∃ w : List E, (∀ e ∈ w, e ∈ S) ∧
      (w.map (totalGenerator D T K a ha X τ S)).prod = g := by
  obtain ⟨w, hw, hv⟩ := g.property
  refine ⟨w, hw, ?_⟩
  apply Subtype.ext
  exact (totalGenerator_product D T K a ha X τ S w hw).trans hv

/-- Equality of augmented raw records implies equality on every retained old
component-permutation coordinate. -/
theorem component_coordinate_eq_of_value_eq
    (p q : List E) (hv :
      value D T K a ha X τ p = value D T K a ha X τ q)
    (i : I) :
    D.componentWordPerm (T i) (a i) (ha i) p =
      D.componentWordPerm (T i) (a i) (ha i) q := by
  have h := congrArg
    (fun z : Product D T K a ha X =>
      MulOpposite.unop ((z.1 i).2)) hv
  exact h

/-- Hence equality of allowed word values in the augmented group is already
the record-compatibility hypothesis used by the reflection theorem. -/
theorem component_record_of_word_eq
    (S : Set E) (p q : List E)
    (hp : ∀ e ∈ p, e ∈ S) (hq : ∀ e ∈ q, e ∈ S)
    (hv :
      (p.map (totalGenerator D T K a ha X τ S)).prod =
      (q.map (totalGenerator D T K a ha X τ S)).prod)
    (i : I) :
    D.componentWordPerm (T i) (a i) (ha i) p =
      D.componentWordPerm (T i) (a i) (ha i) q := by
  have hval := congrArg Subtype.val hv
  rw [totalGenerator_product D T K a ha X τ S p hp,
      totalGenerator_product D T K a ha X τ S q hq] at hval
  exact component_coordinate_eq_of_value_eq D T K a ha X τ p q hval i

/-- Forgetting all new tests gives the old literal record group. -/
noncomputable def forget (S : Set E) :
    imageGroup D T K a ha X τ S →*
      DirectRecord.imageGroup D T K a ha S where
  toFun g := ⟨g.val.1, by
    obtain ⟨w, hw, hv⟩ := g.property
    refine ⟨w, hw, ?_⟩
    exact congrArg Prod.fst hv⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem forget_valuation (S : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) :
    forget D T K a ha X τ S (valuation D T K a ha X τ S w hw) =
      DirectRecord.valuation D T K a ha S w hw := rfl

/-- The new test coordinate is exactly the word action supplied to this step. -/
theorem valuation_test_coordinate (S : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (j : J) :
    MulOpposite.unop
        ((valuation D T K a ha X τ S w hw).val.2 j) =
      MulOpposite.unop (testValue X τ w j) := rfl

end AugmentedRecord
end EdgeGraph
end GluingEPPA.Steiner
