import GluingEPPA.Steiner.RecordInclusion

/-!
# The recursive family of literal valuation records

The carrier at S is constructed recursively as the image of the current
manuscript's record on all proper subsets of S. No older recursive-group
existence theorem is imported. Finiteness, involutions and word generation
are proved during this recursion. The inclusion/deletion compatibility and
exact replacement properties remain separate obligations for this family.

At the empty set the same formula is an empty product and hence the trivial
group. Extending the generator function by 1 outside S is bookkeeping only;
all representation words and all walks still use the prescribed edge set.
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
variable (S : Set E)

/-- Extend named generators by the identity outside their allowed edge set. -/
noncomputable def totalGenerator (e : E) : imageGroup D T K a ha S :=
  if he : e ∈ S then generator D T K a ha S e he else 1

theorem totalGenerator_mem (e : E) (he : e ∈ S) :
    totalGenerator D T K a ha S e = generator D T K a ha S e he := by
  simp only [totalGenerator, dif_pos he]

theorem totalGenerator_not_mem (e : E) (he : e ∉ S) :
    totalGenerator D T K a ha S e = 1 := by
  simp only [totalGenerator, dif_neg he]

theorem totalGenerator_square (e : E) :
    totalGenerator D T K a ha S e * totalGenerator D T K a ha S e = 1 := by
  by_cases he : e ∈ S
  · rw [totalGenerator_mem D T K a ha S e he]
    exact generator_involutive D T K a ha S e he
  · rw [totalGenerator_not_mem D T K a ha S e he, one_mul]

/-- Evaluation in the image group is the literal record, not a new quotient. -/
theorem totalGenerator_product (w : List E) (hw : ∀ e ∈ w, e ∈ S) :
    ((w.map (totalGenerator D T K a ha S)).prod).val = value D T K a ha w := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      have he := hw e (by simp)
      have hw' : ∀ f ∈ w, f ∈ S := fun f hf => hw f (by simp [hf])
      change (totalGenerator D T K a ha S e).val *
        ((w.map (totalGenerator D T K a ha S)).prod).val = value D T K a ha (e :: w)
      rw [totalGenerator_mem D T K a ha S e he]
      change letter D T K a ha e *
        ((w.map (totalGenerator D T K a ha S)).prod).val = value D T K a ha (e :: w)
      rw [ih hw', value_cons]

theorem valuation_eq_product (w : List E) (hw : ∀ e ∈ w, e ∈ S) :
    valuation D T K a ha S w hw = (w.map (totalGenerator D T K a ha S)).prod := by
  apply Subtype.ext
  exact (totalGenerator_product D T K a ha S w hw).symm

/-- Every element has an allowed word representation, unconditionally. -/
theorem image_generated (g : imageGroup D T K a ha S) :
    ∃ w : List E, (∀ e ∈ w, e ∈ S) ∧
      (w.map (totalGenerator D T K a ha S)).prod = g := by
  obtain ⟨w, hw, hv⟩ := g.property
  refine ⟨w, hw, ?_⟩
  apply Subtype.ext
  exact (totalGenerator_product D T K a ha S w hw).trans hv

end DirectRecord

namespace RecursiveRecord

universe u
variable {V E : Type u}

/-- The data needed to form the next literal record; it assumes no replacement. -/
structure Data (E : Type u) (S : Finset E) where
  Carrier : Type u
  [group : Group Carrier]
  [finite : Finite Carrier]
  edge : E → Carrier
  square : ∀ e, edge e * edge e = 1
  outside : ∀ e, e ∉ S → edge e = 1
  generated : ∀ g : Carrier, ∃ w : List E,
    (∀ e ∈ w, e ∈ S) ∧ (w.map edge).prod = g

attribute [instance] Data.group Data.finite

/-- The actual proper subsets, not independently chosen copies of smaller data. -/
abbrev Proper (S : Finset E) := {T : Finset E // T ⊂ S}

variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

namespace Step

variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)

abbrev sets (i : Proper S) : Set E := (i.val : Set E)
abbrev groups (i : Proper S) : Type u := (old i).Carrier
abbrev edges (i : Proper S) : E → groups S old i := (old i).edge

theorem involutions (i : Proper S) (e : E) (_he : e ∈ sets S i) :
    edges S old i e * edges S old i e = 1 := (old i).square e

/-- K_S is exactly the direct image of records built from all earlier K_T. -/
noncomputable def data : Data E S where
  Carrier := DirectRecord.imageGroup D (sets S) (groups S old)
    (edges S old) (involutions S old) (S : Set E)
  group := inferInstance
  finite := by
    classical
    exact DirectRecord.finiteImageGroup D (sets S) (groups S old)
      (edges S old) (involutions S old) (S : Set E)
  edge := DirectRecord.totalGenerator D (sets S) (groups S old)
    (edges S old) (involutions S old) (S : Set E)
  square := DirectRecord.totalGenerator_square D (sets S) (groups S old)
    (edges S old) (involutions S old) (S : Set E)
  outside := DirectRecord.totalGenerator_not_mem D (sets S) (groups S old)
    (edges S old) (involutions S old) (S : Set E)
  generated := DirectRecord.image_generated D (sets S) (groups S old)
    (edges S old) (involutions S old) (S : Set E)

/-- The earlier group coordinate is a genuine homomorphism, before inclusions. -/
def projection (i : Proper S) : (data D S old).Carrier →* (old i).Carrier :=
  DirectRecord.projection D (sets S) (groups S old)
    (edges S old) (involutions S old) (S : Set E) i

theorem projection_edge (i : Proper S) (e : E) (he : e ∈ S) :
    projection D S old i ((data D S old).edge e) =
      if e ∈ i.val then (old i).edge e else 1 := by
  classical
  change DirectRecord.projection D (sets S) (groups S old)
      (edges S old) (involutions S old) (S : Set E) i
      (DirectRecord.totalGenerator D (sets S) (groups S old)
        (edges S old) (involutions S old) (S : Set E) e) = _
  rw [DirectRecord.totalGenerator_mem _ _ _ _ _ _ e he]
  rfl

/-- The coordinate action needed in the next compatibility lemma. -/
def action (i : Proper S) : RightAction (data D S old).Carrier
    (D.Component (sets S i) (edges S old i) (involutions S old i)) :=
  DirectRecord.coordinateAction D (sets S) (groups S old)
    (edges S old) (involutions S old) (S : Set E) i

theorem action_edge (i : Proper S) (e : E) (he : e ∈ S)
    (c : D.Component (sets S i) (edges S old i) (involutions S old i)) :
    (action D S old i).act c ((data D S old).edge e) =
      D.componentEdgePerm (sets S i) (edges S old i) (involutions S old i) e c := by
  change (DirectRecord.coordinateAction D (sets S) (groups S old)
      (edges S old) (involutions S old) (S : Set E) i).act c
      (DirectRecord.totalGenerator D (sets S) (groups S old)
        (edges S old) (involutions S old) (S : Set E) e) = _
  rw [DirectRecord.totalGenerator_mem _ _ _ _ _ _ e he]
  rfl

end Step

/-- Well-founded recursion constructs the same smaller data wherever it is used. -/
noncomputable def family (S : Finset E) : Data E S :=
  Step.data D S (fun i => family D i.val)
termination_by S.card
decreasing_by exact Finset.card_lt_card i.property

/-- The defining equation records the manuscript's exact recursive carrier. -/
theorem family_step (S : Finset E) :
    family D S = Step.data D S (fun i => family D i.val) := by
  rw [family]

/-- In particular no induction hypothesis is needed to obtain the finite groups. -/
theorem family_generated (S : Finset E) (g : (family D S).Carrier) :
    ∃ w : List E, (∀ e ∈ w, e ∈ S) ∧
      (w.map (family D S).edge).prod = g := (family D S).generated g

theorem family_square (S : Finset E) (e : E) :
    (family D S).edge e * (family D S).edge e = 1 := (family D S).square e

/-- The empty-stage instance of the record formula is the trivial group. -/
theorem family_empty_eq_one (g : (family D ∅).Carrier) : g = 1 := by
  obtain ⟨w, hw, hv⟩ := (family D ∅).generated g
  have hw0 : w = [] := by
    cases w with
    | nil => rfl
    | cons e w =>
        have he := hw e (by simp)
        simpa using he
  simpa only [hw0, List.map_nil, List.prod_nil] using hv.symm

end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
