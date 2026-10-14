import GluingEPPA.Sparsening.CompleteRecords
import GluingEPPA.Relational

/-!
The actual varying-size chart quotient. Occurrences are restricted to points
belonging to their chart; there are no isolated artificial outside points.
The fibrewise presentation records the unchanged ambient point explicitly.
-/
namespace GluingEPPA.Sparsening.ChartAtlas
universe u v w z
variable {V : Type u} {E : Type v} {A : Type w}
variable (G : GluingEPPA.EdgeGraph V E) (support : A → V → Prop)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

abbrev Occurrence (x : A) := {p : V × (E → ZMod 2) // support x p.1}

lemma path_symm {K : V → Prop} {p q : V × (E → ZMod 2)}
    (h : Relation.ReflTransGen (restrictedLift G K) p q) :
    Relation.ReflTransGen (restrictedLift G K) q p := by
  induction h with
  | refl => exact .refl
  | @tail q r h step ih =>
    exact (Relation.ReflTransGen.single
      ⟨G.liftEdge_symm step.1, step.2.2, step.2.1⟩).trans ih

lemma path_mono {K H : V → Prop} (incl : ∀ s, K s → H s)
    {p q : V × (E → ZMod 2)}
    (h : Relation.ReflTransGen (restrictedLift G K) p q) :
    Relation.ReflTransGen (restrictedLift G H) p q := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail ⟨step.1, incl _ step.2.1, incl _ step.2.2⟩

def pointSetoid (x : A) : Setoid (Occurrence (E := E) support x) where
  r p q := Relation.ReflTransGen (restrictedLift G (support x)) p.val q.val
  iseqv := ⟨fun _ => .refl, fun h => path_symm G h, fun h k => h.trans k⟩

abbrev Vertex := Σ x : A, Quotient (pointSetoid G support x)

def point (s : V) (chi : E → ZMod 2) (x : A) (hx : support x s) :
    Quotient (pointSetoid G support x) :=
  Quotient.mk _ ⟨(s, chi), hx⟩

def copy (s : V) (chi : E → ZMod 2) (x : A) (hx : support x s) :
    Vertex G support := ⟨x, point G support s chi x hx⟩

def project (q : Vertex G support) : A := q.1

@[simp] theorem project_copy (s : V) (chi : E → ZMod 2) (x : A) (hx : support x s) :
    project G support (copy G support s chi x hx) = x := rfl

theorem copy_injective (s : V) (chi : E → ZMod 2) :
    Function.Injective (fun x : {x // support x s} => copy G support s chi x.val x.property) := by
  intro x y h
  exact Subtype.ext (congrArg (project G support) h)

theorem point_eq_iff (s t : V) (chi psi : E → ZMod 2)
    (x : A) (hs : support x s) (ht : support x t) :
    point G support s chi x hs = point G support t psi x ht ↔
      Relation.ReflTransGen (restrictedLift G (support x)) (s, chi) (t, psi) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem copy_eq_of_path {s t : V} {chi psi : E → ZMod 2}
    (x : A) (hs : support x s) (ht : support x t)
    (h : Relation.ReflTransGen (restrictedLift G (support x)) (s, chi) (t, psi)) :
    copy G support s chi x hs = copy G support t psi x ht := by
  have hp : point G support s chi x hs = point G support t psi x ht := Quotient.sound h
  exact congrArg (fun q : Quotient (pointSetoid G support x) =>
    (⟨x, q⟩ : Vertex G support)) hp

/-- Complete records now classify equality in a quotient of valid occurrences. -/
theorem point_eq_iff_records
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (s t : V) (chi psi : E → ZMod 2) (x : A)
    (hs : support x s) (ht : support x t) :
    point G support s chi x hs = point G support t psi x ht ↔
      charge G (s, chi) = charge G (t, psi) ∧
      ∀ e, ¬ (support x (G.left e) ∧ support x (G.right e)) → chi e = psi e := by
  rw [point_eq_iff]
  exact supported_walk_iff_records G complete (support x) s t hs ht chi psi

/-- Every quotient vertex is genuinely in a chart, including when some charts
are empty. No covering assumption on the ambient set is required. -/
theorem exists_representative (q : Vertex G support) :
    ∃ (s : V) (chi : E → ZMod 2) (h : support (project G support q) s),
      copy G support s chi (project G support q) h = q := by
  rcases q with ⟨x, q⟩
  induction q using Quotient.inductionOn with
  | _ p => exact ⟨p.val.1, p.val.2, p.property, rfl⟩

instance finite_vertex [Finite A] : Finite (Vertex G support) := by
  infer_instance

variable {L : Nat → Type z}

def chartStructure (R : RelStructure L A) (s : V) :
    RelStructure L {x // support x s} where
  rel r x := R.rel r (fun i => (x i).val)

def quotientStructure (R : RelStructure L A) : RelStructure L (Vertex G support) where
  rel r q := ∃ (s : V) (chi : E → ZMod 2) (x : Fin _ → {x // support x s}),
    R.rel r (fun i => (x i).val) ∧
      ∀ i, copy G support s chi (x i).val (x i).property = q i

/-- Chart copies are induced, not just relation-preserving. -/
def chartEmbedding (R : RelStructure L A) (s : V) (chi : E → ZMod 2) :
    Embedding (chartStructure support R s) (quotientStructure G support R) where
  toFun x := copy G support s chi x.val x.property
  injective := copy_injective G support s chi
  rel_iff r x := by
    constructor
    · rintro ⟨t, psi, y, hy, heq⟩
      have hp : (fun i => (y i).val) = (fun i => (x i).val) :=
        funext (fun i => congrArg (project G support) (heq i))
      change R.rel r (fun i => (x i).val)
      simpa only [hp] using hy
    · intro hx
      exact ⟨s, chi, x, hx, fun _ => rfl⟩

/-- The simultaneous supported representative is an actual common chart
for any family of valid occurrences, not only a formal record. -/
theorem common_chart {P : Type*}
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (x : P → A) (origin : P → V) (chi : P → E → ZMod 2)
    (valid : ∀ p, support (x p) (origin p)) (alpha : V → ZMod 2)
    (odd : (∑ v, alpha v) = 1)
    (record : ∀ p v, charge G (origin p, chi p) v = alpha v)
    (consistent : ∀ p q e,
      ¬ (support (x p) (G.left e) ∧ support (x p) (G.right e)) →
      ¬ (support (x q) (G.left e) ∧ support (x q) (G.right e)) → chi p e = chi q e) :
    ∃ (s : V) (c : E → ZMod 2) (valid' : ∀ p, support (x p) s),
      ∀ p, copy G support (origin p) (chi p) (x p) (valid p) =
        copy G support s c (x p) (valid' p) := by
  obtain ⟨s, c, hs, paths⟩ := common_supported_representative G complete
    (fun p => support (x p)) origin chi alpha valid odd record consistent
  exact ⟨s, c, hs, fun p => copy_eq_of_path G support (x p) (valid p) (hs p) (paths p)⟩

end GluingEPPA.Sparsening.ChartAtlas
