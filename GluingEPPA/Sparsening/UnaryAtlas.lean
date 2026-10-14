import GluingEPPA.Sparsening.ChartAtlas
import GluingEPPA.Sparsening.ClosedCuts

/-!
Full unary set-valued functions on the varying-size chart quotient.
Closed charts make output copies independent of the chosen input occurrence.
The projection maps each entire output set ONTO the original output set.
-/
namespace GluingEPPA.Sparsening.ChartAtlas
universe u v w z
variable {V : Type u} {E : Type v} {A : Type w} {F : Type z}
variable (G : GluingEPPA.EdgeGraph V E) (support : A → V → Prop)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (out : F → A → Set A)
variable (closed : ∀ f x y s, support x s → y ∈ out f x → support y s)

/-- Use all valid representatives. The following fibre lemma proves that
this existential definition adds nothing beyond any single representative. -/
def liftOutput (f : F) (q : Vertex G support) : Set (Vertex G support) :=
  {z | ∃ p : Occurrence (E := E) support q.1,
    Quotient.mk (pointSetoid G support q.1) p = q.2 ∧
      ∃ (y : A) (hy : y ∈ out f q.1),
        copy G support p.val.1 p.val.2 y
          (closed f q.1 y p.val.1 p.property hy) = z}

/-- Equality of full fibres, not merely preservation of function-graph edges. -/
theorem liftOutput_copy (f : F) (s : V) (chi : E → ZMod 2)
    (x : A) (hx : support x s) (z : Vertex G support) :
    z ∈ liftOutput G support out closed f (copy G support s chi x hx) ↔
      ∃ (y : A) (hy : y ∈ out f x),
        copy G support s chi y (closed f x y s hx hy) = z := by
  constructor
  · rintro ⟨p, hp, y, hy, hz⟩
    refine ⟨y, hy, ?_⟩
    have hpath : Relation.ReflTransGen (restrictedLift G (support x)) p.val (s, chi) :=
      Quotient.exact hp
    have houtput := path_mono G (fun t ht => closed f x y t ht hy) hpath
    have heq := copy_eq_of_path G support y
      (closed f x y p.val.1 p.property hy) (closed f x y s hx hy) houtput
    exact heq.symm.trans hz
  · rintro ⟨y, hy, hz⟩
    exact ⟨⟨(s, chi), hx⟩, rfl, y, hy, hz⟩

/-- Full-fibre projection at every quotient vertex. -/
theorem liftOutput_projection (f : F) (q : Vertex G support) :
    project G support '' liftOutput G support out closed f q =
      out f (project G support q) := by
  obtain ⟨s, chi, hx, hq⟩ := exists_representative G support q
  have hgeneral : ∀ (x : A) (h : support x s),
      project G support '' liftOutput G support out closed f (copy G support s chi x h) =
        out f x := by
    intro x h
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      obtain ⟨y', hy', hc⟩ := (liftOutput_copy G support out closed f s chi x h z).mp hz
      have heq : y' = y := (congrArg (project G support) hc).trans hzy
      exact heq ▸ hy'
    · intro hy
      refine ⟨copy G support s chi y (closed f x y s h hy), ?_, rfl⟩
      exact (liftOutput_copy G support out closed f s chi x h _).mpr ⟨y, hy, rfl⟩
  have hh := hgeneral (project G support q) hx
  rw [hq] at hh
  exact hh

/-- Each lifted chart is closed under all unary outputs. -/
theorem lifted_chart_closed (s : V) (chi : E → ZMod 2) :
    UnaryClosed (liftOutput G support out closed)
      (fun q => ∃ (x : A) (hx : support x s), copy G support s chi x hx = q) := by
  intro f q z hq hz
  obtain ⟨x, hx, rfl⟩ := hq
  obtain ⟨y, hy, heq⟩ := (liftOutput_copy G support out closed f s chi x hx z).mp hz
  exact ⟨y, closed f x y s hx hy, heq⟩

/-- The lifted unary functions satisfy the support-monotonicity premise
of the closed-cut argument, derived here from concrete quotient fibres. -/
theorem output_support_mono (f : F) (q z : Vertex G support)
    (hz : z ∈ liftOutput G support out closed f q)
    (s : V) (hs : support (project G support q) s) :
    support (project G support z) s := by
  have himg : project G support z ∈
      project G support '' liftOutput G support out closed f q := ⟨z, hz, rfl⟩
  rw [liftOutput_projection G support out closed f q] at himg
  exact closed f (project G support q) (project G support z) s hs himg

end GluingEPPA.Sparsening.ChartAtlas
