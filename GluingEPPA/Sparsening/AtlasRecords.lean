import GluingEPPA.Sparsening.UnaryAtlas

/-!
Intrinsic records on the valid-occurrence quotient, with relation and unary
agreement proved from actual chart contributions rather than assumed.
-/
namespace GluingEPPA.Sparsening.ChartAtlas
universe u v w z t
variable {V : Type u} {E : Type v} {A : Type w}
variable (G : GluingEPPA.EdgeGraph V E) (support : A → V → Prop)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def pointCharge (x : A) : Quotient (pointSetoid G support x) → (V → ZMod 2) :=
  Quotient.lift (fun p => charge G p.val)
    (fun _ _ h => charge_path G (restricted_path_forget G h))

def atlasCharge (q : Vertex G support) : V → ZMod 2 :=
  pointCharge G support q.1 q.2

@[simp] theorem atlasCharge_copy (s : V) (chi : E → ZMod 2)
    (x : A) (hx : support x s) :
    atlasCharge G support (copy G support s chi x hx) = charge G (s, chi) := rfl

theorem atlasCharge_odd (q : Vertex G support) :
    (∑ v, atlasCharge G support q v) = 1 := by
  rcases q with ⟨x, q⟩
  induction q using Quotient.inductionOn with
  | _ p => exact charge_odd G p.val

def pointExterior (x : A) (e : E)
    (outside : ¬ (support x (G.left e) ∧ support x (G.right e))) :
    Quotient (pointSetoid G support x) → ZMod 2 :=
  Quotient.lift (fun p => p.val.2 e)
    (fun _ _ h => exterior_path G (support x) e outside h)

/-- A total record function with a dummy zero on internal coordinates.
Only its values at exterior coordinates have geometric meaning. -/
noncomputable def atlasExterior (q : Vertex G support) (e : E) : ZMod 2 := by
  classical
  exact if h : ¬ (support q.1 (G.left e) ∧ support q.1 (G.right e)) then
    pointExterior G support q.1 e h q.2 else 0

theorem atlasExterior_copy (s : V) (chi : E → ZMod 2)
    (x : A) (hx : support x s) (e : E)
    (outside : ¬ (support x (G.left e) ∧ support x (G.right e))) :
    atlasExterior G support (copy G support s chi x hx) e = chi e := by
  classical
  simp [atlasExterior, copy, pointExterior, point, outside]

/-- The auxiliary complete-chart relation, independently of a chosen symbol J. -/
def CoChart (p q : Vertex G support) : Prop :=
  ∃ (s : V) (chi : E → ZMod 2) (x y : A) (hx : support x s) (hy : support y s),
    copy G support s chi x hx = p ∧ copy G support s chi y hy = q

theorem coChart_charge {p q : Vertex G support} (h : CoChart G support p q) :
    atlasCharge G support p = atlasCharge G support q := by
  obtain ⟨s, chi, x, y, hx, hy, hp, hq⟩ := h
  rw [← hp, ← hq, atlasCharge_copy, atlasCharge_copy]

theorem coChart_path_charge {p q : Vertex G support}
    (h : Relation.ReflTransGen (CoChart G support) p q) :
    atlasCharge G support p = atlasCharge G support q := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.trans (coChart_charge G support step)

theorem coChart_exterior {p q : Vertex G support} (h : CoChart G support p q)
    (e : E)
    (hp : ¬ (support (project G support p) (G.left e) ∧
      support (project G support p) (G.right e)))
    (hq : ¬ (support (project G support q) (G.left e) ∧
      support (project G support q) (G.right e))) :
    atlasExterior G support p e = atlasExterior G support q e := by
  obtain ⟨s, chi, x, y, hx, hy, hpx, hqy⟩ := h
  have hxe : ¬ (support x (G.left e) ∧ support x (G.right e)) := by
    simpa only [← hpx, project_copy] using hp
  have hye : ¬ (support y (G.left e) ∧ support y (G.right e)) := by
    simpa only [← hqy, project_copy] using hq
  rw [← hpx, ← hqy, atlasExterior_copy G support s chi x hx e hxe,
    atlasExterior_copy G support s chi y hy e hye]

variable {L : Nat → Type z}

theorem relation_coChart (R : RelStructure L A) {n : Nat}
    (r : L n) (q : Fin n → Vertex G support)
    (h : (quotientStructure G support R).rel r q) (i j : Fin n) :
    CoChart G support (q i) (q j) := by
  obtain ⟨s, chi, x, _, heq⟩ := h
  exact ⟨s, chi, (x i).val, (x j).val, (x i).property,
    (x j).property, heq i, heq j⟩

variable {F : Type t} (out : F → A → Set A)
variable (closed : ∀ f x y s, support x s → y ∈ out f x → support y s)

theorem output_coChart (f : F) (q z : Vertex G support)
    (h : z ∈ liftOutput G support out closed f q) : CoChart G support q z := by
  obtain ⟨s, chi, hx, hq⟩ := exists_representative G support q
  have hz : z ∈ liftOutput G support out closed f
      (copy G support s chi (project G support q) hx) := by
    rw [hq]
    exact h
  obtain ⟨y, hy, heq⟩ := (liftOutput_copy G support out closed f s chi
    (project G support q) hx z).mp hz
  exact ⟨s, chi, project G support q, y, hx,
    closed f (project G support q) y s hx hy, hq, heq⟩

/-- Concrete unary exterior agreement required by the separator theorem. -/
theorem output_exterior (f : F) (q z : Vertex G support)
    (h : z ∈ liftOutput G support out closed f q) (e : E)
    (hq : ¬ (support (project G support q) (G.left e) ∧
      support (project G support q) (G.right e)))
    (hz : ¬ (support (project G support z) (G.left e) ∧
      support (project G support z) (G.right e))) :
    atlasExterior G support q e = atlasExterior G support z e :=
  coChart_exterior G support (output_coChart G support out closed f q z h) e hq hz

end GluingEPPA.Sparsening.ChartAtlas
