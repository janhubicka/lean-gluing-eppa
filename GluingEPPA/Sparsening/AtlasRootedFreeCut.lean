import GluingEPPA.Sparsening.AtlasAllTestCuts

/-!
# The actual atlas free cut has an old J-complete projected root

The chart-or-free-cut theorem alone loses which old charts contain the
root. The strengthened result below recovers precisely what the local
tree induction needs: either one common lifted chart, or a genuine
closed unary free decomposition whose projected common root has
complete old J. The distinct-charge cut has empty root; the
equal-charge cut has root in BOTH endpoint charts.

No injectivity of the quotient projection is assumed, nor is the
projected old image declared free. A separate lemma proves that the
projected common root is closed under all old unary function values.
-/

namespace GluingEPPA.Sparsening.ChartAtlas

universe u v w z t
variable {V : Type u} {E : Type v} {A : Type w}
variable {L : Nat → Type z} {F : Type t}
variable (G : GluingEPPA.EdgeGraph V E) (support : A → V → Prop)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (R : RelStructure L A) (out : F → A → Set A)
variable (closed : ∀ f x y s, support x s → y ∈ out f x → support y s)

/-- An actual source free cut whose overlap projects to an old J-clique.
For empty overlap the clique conclusion is vacuous. -/
theorem atlas_chart_or_JRoot_freeCut
    (complete : ∀ s t : V, s ≠ t → ∃ e, G.Inc e s t)
    (J : A → A → Prop)
    (chart_J : ∀ s x y, support x s → support y s → J x y)
    (X : Set (Vertex G support)) [Nonempty X] :
    (∃ (s : V) (chi : E → ZMod 2), ∀ q : X,
      ∃ hx : support (project G support q.val) s,
        copy G support s chi (project G support q.val) hx = q.val) ∨
    (∃ d : UnaryFreeDecomposition
      (inducedAtlas G support R X)
      (inducedOutput G support out closed X),
      ∀ (p q : X),
        p ∈ d.left → p ∈ d.right →
        q ∈ d.left → q ∈ d.right →
        J (project G support p.val) (project G support q.val)) := by
  classical
  have hrel : ∀ {n} (r : L n) (xs : Fin n → X),
      (inducedAtlas G support R X).rel r xs →
      ∀ i j, atlasCharge G support (xs i).val =
        atlasCharge G support (xs j).val := by
    intro n r xs hr i j
    exact coChart_charge G support
      (relation_coChart G support R r (fun k => (xs k).val) hr i j)
  have hunary : ∀ f (p q : X),
      q ∈ inducedOutput G support out closed X f p →
      atlasCharge G support q.val = atlasCharge G support p.val := by
    intro f p q h
    exact (coChart_charge G support
      (output_coChart G support out closed f p.val q.val h)).symm
  by_cases hconstant : ∀ p q : X,
      atlasCharge G support p.val = atlasCharge G support q.val
  · rcases atlas_chart_or_closed_cut G support R out closed complete X hconstant with
      hchart | hcut
    · exact Or.inl hchart
    · obtain ⟨e, ⟨cut⟩⟩ := hcut
      right
      refine ⟨cut.toFreeDecomposition, ?_⟩
      intro p q hpL hpR hqL hqR
      have hp : support (project G support p.val) (G.left e) :=
        ((cut.intersection p).mp ⟨hpL, hpR⟩).1
      have hq : support (project G support q.val) (G.left e) :=
        ((cut.intersection q).mp ⟨hqL, hqR⟩).1
      exact chart_J (G.left e) (project G support p.val)
        (project G support q.val) hp hq
  · simp only [not_forall] at hconstant
    obtain ⟨p, q, hpq⟩ := hconstant
    let d := freeCut_of_nonconstant_color
      (inducedAtlas G support R X)
      (inducedOutput G support out closed X)
      (fun z : X => atlasCharge G support z.val) hrel hunary p q hpq
    right
    refine ⟨d, ?_⟩
    intro a b haL haR hbL hbR
    have heq : atlasCharge G support a.val =
        atlasCharge G support p.val := haL
    have hneq : atlasCharge G support a.val ≠
        atlasCharge G support p.val := haR
    exact (hneq heq).elim

/-- The actual intersection of the closed source sides projects to a
closed OLD substructure. The cut need not be free downstairs.
This does not require completeness of J or nonempty root. -/
theorem freeCut_projected_root_closed
    (X : Set (Vertex G support))
    (hX : UnaryClosed (liftOutput G support out closed)
      (fun q => q ∈ X))
    (d : UnaryFreeDecomposition
      (inducedAtlas G support R X)
      (inducedOutput G support out closed X)) :
    UnaryClosed out
      (fun x => x ∈ project G support ''
        {q : Vertex G support |
          ∃ z : X, z ∈ d.left ∧ z ∈ d.right ∧ z.val = q}) := by
  let root : Set (Vertex G support) :=
    {q | ∃ z : X, z ∈ d.left ∧ z ∈ d.right ∧ z.val = q}
  have hroot : UnaryClosed (liftOutput G support out closed)
      (fun q => q ∈ root) := by
    intro f q y hq hy
    obtain ⟨z, hzL, hzR, heq⟩ := hq
    subst q
    have hyX : y ∈ X := hX f z.val y z.property hy
    refine ⟨⟨y, hyX⟩, ?_, ?_, rfl⟩
    · exact d.left_closed f z ⟨y, hyX⟩ hzL hy
    · exact d.right_closed f z ⟨y, hyX⟩ hzR hy
  exact project_closed G support out closed root hroot

end GluingEPPA.Sparsening.ChartAtlas
