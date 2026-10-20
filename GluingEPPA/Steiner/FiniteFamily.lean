import GluingEPPA.Steiner.FamilyStep

/-!
# The actual finite family of groups

The group attached to an edge subset is defined by well-founded recursion,
not supplied as an existence hypothesis. Only proper subsets enter its product.
The compatibility and walk-replacement properties are proved separately.
-/

namespace GluingEPPA.Steiner.FiniteFamily

universe u
variable {V E : Type u} [Fintype E] [DecidableEq E] [Finite V]
attribute [local instance] Classical.propDecidable

abbrev Proper (S : Finset E) := {R : Finset E // R ⊂ S}

/-- The intrinsic finite-group data. Edges outside the specified set have
value one; generation uses only the specified edge names. -/
structure Data (E : Type u) (S : Finset E) where
  Carrier : Type u
  [group : Group Carrier]
  [finite : Finite Carrier]
  edge : E → Carrier
  involutive : ∀ e, edge e * edge e = 1
  outside : ∀ e, e ∉ S → edge e = 1
  generated : ∀ g, ∃ w : List S, wordValue (fun e : S => edge e.val) w = g

attribute [instance] Data.group Data.finite

namespace Data

variable {S : Finset E} (d : Data E S)

def transport (D : EdgeGraph V E) : Transport V d.Carrier :=
  D.transport (↑S : Set E) d.edge (fun e _ => d.involutive e)

end Data

namespace Step

variable (D : EdgeGraph V E) (S : Finset E) (old : ∀ R : Proper S, Data E R.val)

abbrev Groups (r : Proper S) := (old r).Carrier

abbrev transports (r : Proper S) : Transport V (Groups S old r) :=
  (old r).transport D

abbrev masks (r : Proper S) : Set E := ↑r.val

abbrev edges (r : Proper S) : E → Groups S old r := (old r).edge

abbrev Ambient := RecursiveStep.Product (Groups S old) (transports D S old)

noncomputable def value (e : E) : Ambient D S old :=
  RecursiveStep.edgeValue (Groups S old) (transports D S old)
    (masks S) (edges S old) D e

theorem value_involutive (e : E) : value D S old e * value D S old e = 1 :=
  RecursiveStep.edgeValue_involutive (Groups S old) (transports D S old)
    (masks S) (edges S old) D (fun r e _ => (old r).involutive e) e

/-- Generate the next group using the current subset, not all ambient edges. -/
noncomputable abbrev Group := GeneratedStep.Carrier
  (fun e : S => value D S old e.val)
  (fun e : S => value_involutive D S old e.val)

noncomputable def edge (e : E) : Group D S old :=
  if he : e ∈ S then GeneratedStep.generator
    (fun e : S => value D S old e.val)
    (fun e : S => value_involutive D S old e.val) ⟨e, he⟩ else 1

@[simp] theorem edge_of_mem (e : E) (he : e ∈ S) :
    edge D S old e = GeneratedStep.generator
      (fun e : S => value D S old e.val)
      (fun e : S => value_involutive D S old e.val) ⟨e, he⟩ := by
  simp only [edge, dif_pos he]

@[simp] theorem edge_of_not_mem (e : E) (he : e ∉ S) : edge D S old e = 1 := by
  simp only [edge, dif_neg he]

theorem edge_involutive (e : E) : edge D S old e * edge D S old e = 1 := by
  by_cases he : e ∈ S
  · rw [edge_of_mem D S old e he]
    exact GeneratedStep.generator_involutive
      (fun f : S => value D S old f.val)
      (fun f : S => value_involutive D S old f.val) (⟨e, he⟩ : S)
  · simp only [edge_of_not_mem D S old e he, one_mul]

theorem generated (g : Group D S old) :
    ∃ w : List S, wordValue (fun e : S => edge D S old e.val) w = g := by
  have he : (fun e : S => edge D S old e.val) =
      GeneratedStep.generator
        (fun e : S => value D S old e.val)
        (fun e : S => value_involutive D S old e.val) := by
    funext e
    exact edge_of_mem D S old e.val e.property
  rw [he]
  exact GeneratedStep.generated _ _ g

noncomputable def data : Data E S where
  Carrier := Group D S old
  group := inferInstance
  finite := inferInstance
  edge := edge D S old
  involutive := edge_involutive D S old
  outside := edge_of_not_mem D S old
  generated := generated D S old

end Step

/-- This is a terminating recursion over proper finite edge subsets. No
walk-replacement or compatibility assertion is assumed to define the family. -/
noncomputable def family (D : EdgeGraph V E) : (S : Finset E) → Data E S :=
  Finset.strongInduction fun S ih => Step.data D S (fun R => ih R.val R.property)

theorem family_eq (D : EdgeGraph V E) (S : Finset E) :
    family D S = Step.data D S (fun R => family D R.val) := by
  exact Finset.strongInduction_eq
    (fun S ih => Step.data D S (fun R => ih R.val R.property)) S

/-- Every group in the recursively defined family is finite. -/
theorem family_finite (D : EdgeGraph V E) (S : Finset E) :
    Finite (family D S).Carrier := inferInstance

theorem family_generated (D : EdgeGraph V E) (S : Finset E)
    (g : (family D S).Carrier) :
    ∃ w : List S, wordValue (fun e : S => (family D S).edge e.val) w = g :=
  (family D S).generated g

/-- The initial group is genuinely trivial, as a consequence of generation. -/
theorem family_empty_one (D : EdgeGraph V E)
    (g : (family D (∅ : Finset E)).Carrier) : g = 1 := by
  obtain ⟨w, hw⟩ := (family D (∅ : Finset E)).generated g
  have hnil : w = [] := by
    cases w with
    | nil => rfl
    | cons e w =>
      rcases e with ⟨x, hx⟩
      simp at hx
  simpa only [hnil, wordValue_nil] using hw.symm

end GluingEPPA.Steiner.FiniteFamily
