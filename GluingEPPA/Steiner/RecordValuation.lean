import GluingEPPA.Steiner.ComponentCompatibility

/-!
# The literal direct valuation record in the current manuscript

Given the already constructed groups K_T, form exactly the record
  ((nu_T(w restricted to T), tau_w^T))_T.
Its image on S-words is defined as a subgroup, rather than replaced by a
previous existence theorem. The component permutation factors use opposite
multiplication to implement the manuscript's left-to-right word convention.

This is one construction step. The simultaneous induction, earlier-group
inclusions, and replacement property are not assumed as conclusions here.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace DirectRecord

attribute [local instance] Classical.propDecidable

universe u v w z
variable {V : Type u} {E : Type v} {I : Type z}
variable (D : EdgeGraph V E) (T : I → Set E) (K : I → Type w)
variable [∀ i, Group (K i)]
variable (a : ∀ i, E → K i) (ha : ∀ i e, e ∈ T i → a i e * a i e = 1)

/-- The full product in equation (product), with right permutation order. -/
abbrev Product := ∀ i, K i × (Equiv.Perm (D.Component (T i) (a i) (ha i)))ᵐᵒᵖ

/-- Delete letters outside the chosen edge set; this is a word, not a walk. -/
noncomputable def restrictWord (M : Set E) (w : List E) : List E :=
  w.filter (fun e => decide (e ∈ M))

theorem restrictWord_eq_of_letters (M : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ M) : restrictWord M w = w := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      have he : e ∈ M := hw e (by simp)
      have hw' : ∀ f ∈ w, f ∈ M := fun f hf => hw f (by simp [hf])
      simpa [restrictWord, he] using congrArg (List.cons e) (ih hw')

/-- The direct record, defined coordinate by coordinate as in the paper. -/
noncomputable def value (w : List E) : Product D T K a ha := fun i =>
  (((restrictWord (T i) w).map (a i)).prod,
   MulOpposite.op (D.componentWordPerm (T i) (a i) (ha i) w))

/-- The record assigned to a single edge. -/
noncomputable def letter (e : E) : Product D T K a ha := fun i =>
  (if e ∈ T i then a i e else 1,
   MulOpposite.op (D.componentEdgePerm (T i) (a i) (ha i) e))

@[simp] theorem value_nil : value D T K a ha [] = 1 := rfl

theorem value_cons (e : E) (w : List E) :
    value D T K a ha (e :: w) = letter D T K a ha e * value D T K a ha w := by
  funext i
  apply Prod.ext
  · by_cases he : e ∈ T i <;> simp [value, letter, restrictWord, he]
  · apply MulOpposite.unop_injective
    ext c
    rfl

theorem value_append (p q : List E) :
    value D T K a ha (p ++ q) = value D T K a ha p * value D T K a ha q := by
  induction p with
  | nil => simp only [List.nil_append, value_nil, one_mul]
  | cons e p ih => simp only [List.cons_append, value_cons, ih, mul_assoc]

theorem letter_involutive (e : E) :
    letter D T K a ha e * letter D T K a ha e = 1 := by
  funext i
  apply Prod.ext
  · by_cases he : e ∈ T i <;> simp [letter, he, ha i e]
  · apply MulOpposite.unop_injective
    ext c
    exact D.componentEdgePerm_involutive (T i) (a i) (ha i) e c

theorem letter_inv (e : E) :
    (letter D T K a ha e)⁻¹ = letter D T K a ha e := by
  have h := letter_involutive D T K a ha e
  calc
    (letter D T K a ha e)⁻¹ = (letter D T K a ha e)⁻¹ * 1 := (mul_one _).symm
    _ = (letter D T K a ha e)⁻¹ *
        (letter D T K a ha e * letter D T K a ha e) := by rw [h]
    _ = letter D T K a ha e := by group

theorem value_reverse (w : List E) :
    value D T K a ha w.reverse = (value D T K a ha w)⁻¹ := by
  induction w with
  | nil => simp only [List.reverse_nil, value_nil, inv_one]
  | cons e w ih =>
      simp only [List.reverse_cons, value_append, value_cons, value_nil,
        mul_one, ih, mul_inv_rev, letter_inv]

/-- The new group is literally the image of the record on allowed words. -/
noncomputable def imageGroup (S : Set E) : Subgroup (Product D T K a ha) where
  carrier := {g | ∃ w, (∀ e ∈ w, e ∈ S) ∧ value D T K a ha w = g}
  one_mem' := ⟨[], by simp, value_nil D T K a ha⟩
  mul_mem' := by
    rintro g h ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    refine ⟨p ++ q, ?_, value_append D T K a ha p q⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hp e he
    · exact hq e he
  inv_mem' := by
    rintro g ⟨w, hw, rfl⟩
    refine ⟨w.reverse, ?_, value_reverse D T K a ha w⟩
    intro e he
    exact hw e (by simpa using he)

instance finiteImageGroup [Finite I] [Finite V] [∀ i, Finite (K i)] (S : Set E) :
    Finite (imageGroup D T K a ha S) := by
  infer_instance

/-- A word's record as an element of the new image group. -/
noncomputable def valuation (S : Set E) (w : List E) (hw : ∀ e ∈ w, e ∈ S) :
    imageGroup D T K a ha S := ⟨value D T K a ha w, ⟨w, hw, rfl⟩⟩

theorem valuation_group_coordinate (S : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (i : I) :
    ((valuation D T K a ha S w hw).val i).1 =
      ((restrictWord (T i) w).map (a i)).prod := rfl

theorem valuation_component_coordinate (S : Set E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (i : I) :
    MulOpposite.unop (((valuation D T K a ha S w hw).val i).2) =
      D.componentWordPerm (T i) (a i) (ha i) w := rfl

/-- The named involutive generator a_e^S of the image group. -/
noncomputable def generator (S : Set E) (e : E) (he : e ∈ S) :
    imageGroup D T K a ha S :=
  ⟨letter D T K a ha e, ⟨[e], by
    intro f hf
    have hfe : f = e := by simpa only [List.mem_singleton] using hf
    simpa only [hfe] using he, by
    simp only [value_cons, value_nil, mul_one]⟩⟩

theorem generator_involutive (S : Set E) (e : E) (he : e ∈ S) :
    generator D T K a ha S e he * generator D T K a ha S e he = 1 := by
  apply Subtype.ext
  exact letter_involutive D T K a ha e

/-- The deletion homomorphism is the first coordinate projection. -/
def projection (S : Set E) (i : I) : imageGroup D T K a ha S →* K i where
  toFun g := (g.val i).1
  map_one' := rfl
  map_mul' g h := rfl

theorem projection_generator (S : Set E) (i : I) (e : E) (he : e ∈ S) :
    projection D T K a ha S i (generator D T K a ha S e he) =
      if e ∈ T i then a i e else 1 := rfl

/-- Surjectivity uses only the earlier group's word representation property,
not the new inclusion whose well-definedness is still to be proved. -/
theorem projection_surjective (S : Set E) (i : I) (hTi : T i ⊆ S)
    (hgen : ∀ g : K i, ∃ w : List E,
      (∀ e ∈ w, e ∈ T i) ∧ (w.map (a i)).prod = g) :
    Function.Surjective (projection D T K a ha S i) := by
  intro g
  obtain ⟨w, hw, hv⟩ := hgen g
  refine ⟨valuation D T K a ha S w (fun e he => hTi (hw e he)), ?_⟩
  change ((restrictWord (T i) w).map (a i)).prod = g
  rw [restrictWord_eq_of_letters (T i) w hw, hv]

/-- Projection to a permutation coordinate gives the earlier coordinate action
needed as input to the two-part action. The order is checked definitionally. -/
def coordinateAction (S : Set E) (i : I) :
    RightAction (imageGroup D T K a ha S) (D.Component (T i) (a i) (ha i)) where
  act c g := MulOpposite.unop ((g.val i).2) c
  one c := rfl
  mul c g h := rfl

theorem coordinateAction_word (S : Set E) (i : I) (w : List E)
    (hw : ∀ e ∈ w, e ∈ S) (c : D.Component (T i) (a i) (ha i)) :
    (coordinateAction D T K a ha S i).act c (valuation D T K a ha S w hw) =
      D.componentWordPerm (T i) (a i) (ha i) w c := rfl

theorem coordinateAction_generator (S : Set E) (i : I) (e : E)
    (he : e ∈ S) (c : D.Component (T i) (a i) (ha i)) :
    (coordinateAction D T K a ha S i).act c (generator D T K a ha S e he) =
      D.componentEdgePerm (T i) (a i) (ha i) e c := rfl

end DirectRecord
end EdgeGraph
end GluingEPPA.Steiner
