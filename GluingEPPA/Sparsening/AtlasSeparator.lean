import GluingEPPA.Sparsening.AtlasRecords

/-!
The record-level dichotomy is instantiated for the actual varying-chart
quotient. Its local agreement premises are derived from quotient relations and
full unary fibres. No chart-containment or separator premise is postulated.
-/
namespace GluingEPPA.Sparsening.ChartAtlas
universe u v w z t
variable {V : Type u} {E : Type v} {A : Type w}
variable (G : GluingEPPA.EdgeGraph V E) (support : A → V → Prop)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {L : Nat → Type z} {F : Type t}
variable (R : RelStructure L A) (out : F → A → Set A)
variable (closed : ∀ f x y s, support x s → y ∈ out f x → support y s)

def inducedAtlas (X : Set (Vertex G support)) : RelStructure L X where
  rel r q := (quotientStructure G support R).rel r (fun i => (q i).val)

def inducedOutput (X : Set (Vertex G support)) (f : F) (q : X) : Set X :=
  {z | z.val ∈ liftOutput G support out closed f q.val}

/-- Restriction to a closed test loses no unary values. -/
theorem inducedOutput_full (X : Set (Vertex G support))
    (hclosed : UnaryClosed (liftOutput G support out closed) (fun q => q ∈ X))
    (f : F) (q : X) :
    Subtype.val '' inducedOutput G support out closed X f q =
      liftOutput G support out closed f q.val := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hz
    exact ⟨⟨z, hclosed f q.val z q.property hz⟩, hz, rfl⟩

/-- Full-fibre projection sends every closed test to a closed old set. -/
theorem project_closed (X : Set (Vertex G support))
    (hclosed : UnaryClosed (liftOutput G support out closed) (fun q => q ∈ X)) :
    UnaryClosed out (fun x => x ∈ project G support '' X) := by
  intro f x y hx hy
  obtain ⟨q, hq, rfl⟩ := hx
  rw [← liftOutput_projection G support out closed f q] at hy
  obtain ⟨z, hz, heq⟩ := hy
  exact ⟨z, hclosed f q z hq hz, heq⟩

/-- Concrete chart-or-cut on a nonempty constant-charge test. In particular
this applies to every test connected in the auxiliary chart relation J. -/
theorem atlas_chart_or_closed_cut
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (X : Set (Vertex G support)) [Nonempty X]
    (same_charge : ∀ p q : X, atlasCharge G support p.val = atlasCharge G support q.val) :
    (∃ (s : V) (c : E → ZMod 2), ∀ q : X,
      ∃ h : support (project G support q.val) s,
        copy G support s c (project G support q.val) h = q.val) ∨
    (∃ e : E, Nonempty (ClosedCut (inducedAtlas G support R X)
      (inducedOutput G support out closed X)
      (fun q : X => support (project G support q.val) (G.left e) ∧
        support (project G support q.val) (G.right e)))) := by
  classical
  let q0 : X := Classical.choice inferInstance
  let alpha := atlasCharge G support q0.val
  let sp : X → V → Prop := fun q => support (project G support q.val)
  choose origin chi valid reps using (fun q : X => exists_representative G support q.val)
  have hrecord : ∀ q v, boundary G (chi q) v +
      (if origin q = v then 1 else 0) = alpha v := by
    intro q v
    have hrep : charge G (origin q, chi q) = atlasCharge G support q.val :=
      congrArg (atlasCharge G support) (reps q)
    exact congrFun (hrep.trans (same_charge q q0)) v
  have hext : ∀ q e, ¬ internal G sp q e →
      chi q e = atlasExterior G support q.val e := by
    intro q e he
    have hrep := congrArg (fun z => atlasExterior G support z e) (reps q)
    exact (atlasExterior_copy G support (origin q) (chi q)
      (project G support q.val) (valid q) e he).symm.trans hrep
  have hsmono : ∀ f x y, y ∈ inducedOutput G support out closed X f x →
      ∀ v, sp x v → sp y v := by
    intro f x y hy v hv
    exact output_support_mono G support out closed f x.val y.val hy v hv
  have husame : ∀ f x y, y ∈ inducedOutput G support out closed X f x →
      ∀ e, ¬ internal G sp x e → ¬ internal G sp y e → chi x e = chi y e := by
    intro f x y hy e hx he
    exact (hext x e hx).trans
      ((output_exterior G support out closed f x.val y.val hy e hx he).trans
        (hext y e he).symm)
  have hrsame : ∀ {n} (r : L n) (x : Fin n → X),
      (inducedAtlas G support R X).rel r x →
      ∀ i j e, ¬ internal G sp (x i) e → ¬ internal G sp (x j) e →
        chi (x i) e = chi (x j) e := by
    intro n r x hx i j e hi hj
    have hpair := relation_coChart G support R r (fun k => (x k).val) hx i j
    exact (hext (x i) e hi).trans
      ((coChart_exterior G support hpair e hi hj).trans (hext (x j) e hj).symm)
  have result := record_chart_or_closed_cut G complete sp origin chi alpha valid
    (atlasCharge_odd G support q0.val) hrecord (inducedAtlas G support R X)
    (inducedOutput G support out closed X) hsmono husame hrsame
  rcases result with hchart | hcut
  · left
    obtain ⟨s, c, hs, he, hb⟩ := hchart
    refine ⟨s, c, ?_⟩
    intro q
    refine ⟨hs q, ?_⟩
    have hcharge : charge G (origin q, chi q) = charge G (s, c) := by
      funext v
      exact (hrecord q v).trans (hb v).symm
    have hpath := supported_walk_of_records G complete (sp q) (origin q) s
      (valid q) (hs q) (chi q) c hcharge (fun e hout => (he q e hout).symm)
    have heq := copy_eq_of_path G support (project G support q.val)
      (valid q) (hs q) hpath
    exact heq.symm.trans (reps q)
  · exact Or.inr hcut

/-- Connectivity supplies the common charge; there is no global consistency
assumption on the exterior coordinates. Their disagreement produces the cut. -/
theorem connected_atlas_chart_or_closed_cut
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (X : Set (Vertex G support)) [Nonempty X]
    (connected : ∀ p q : X,
      Relation.ReflTransGen (CoChart G support) p.val q.val) :
    (∃ (s : V) (c : E → ZMod 2), ∀ q : X,
      ∃ h : support (project G support q.val) s,
        copy G support s c (project G support q.val) h = q.val) ∨
    (∃ e : E, Nonempty (ClosedCut (inducedAtlas G support R X)
      (inducedOutput G support out closed X)
      (fun q : X => support (project G support q.val) (G.left e) ∧
        support (project G support q.val) (G.right e)))) :=
  atlas_chart_or_closed_cut G support R out closed complete X
    (fun p q => coChart_path_charge G support (connected p q))

/-- Closure of a side in a closed induced test is actual ambient closure. -/
theorem induced_closed_ambient (X : Set (Vertex G support))
    (hclosed : UnaryClosed (liftOutput G support out closed) (fun q => q ∈ X))
    (side : X → Prop)
    (hside : UnaryClosed (inducedOutput G support out closed X) side) :
    UnaryClosed (liftOutput G support out closed)
      (fun q => ∃ p : X, side p ∧ p.val = q) := by
  intro f q z hq hz
  obtain ⟨p, hp, rfl⟩ := hq
  have hzx := hclosed f p.val z p.property hz
  exact ⟨⟨z, hzx⟩, hside f p ⟨z, hzx⟩ hp hz, rfl⟩

/-- The actual separator root is closed in the ambient quotient. -/
theorem separator_root_closed (X : Set (Vertex G support))
    (hclosed : UnaryClosed (liftOutput G support out closed) (fun q => q ∈ X)) (e : E) :
    UnaryClosed (liftOutput G support out closed)
      (fun q => q ∈ X ∧ support (project G support q) (G.left e) ∧
        support (project G support q) (G.right e)) := by
  intro f q z hq hz
  exact ⟨hclosed f q z hq.1 hz,
    output_support_mono G support out closed f q z hz (G.left e) hq.2.1,
    output_support_mono G support out closed f q z hz (G.right e) hq.2.2⟩

/-- The projected separator is a closed old set; by its definition it lies
in both endpoint charts. This is the root used by the local-tree induction. -/
theorem separator_root_projection_closed (X : Set (Vertex G support))
    (hclosed : UnaryClosed (liftOutput G support out closed) (fun q => q ∈ X)) (e : E) :
    UnaryClosed out (fun x => x ∈ project G support ''
      {q | q ∈ X ∧ support (project G support q) (G.left e) ∧
        support (project G support q) (G.right e)}) :=
  project_closed G support out closed _
    (separator_root_closed G support out closed X hclosed e)

end GluingEPPA.Sparsening.ChartAtlas
