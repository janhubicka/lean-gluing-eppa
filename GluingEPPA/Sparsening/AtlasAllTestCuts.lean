import GluingEPPA.Sparsening.AtlasIrreducible

/-!
# Every small atlas test has a chart or a genuine free decomposition

The separator induction needs no auxiliary J-connectedness hypothesis:
different pointed charges give a free decomposition over the empty root,
while equal charges use the previously verified exterior-coordinate cut.

The FreeDecomposition semantics is the unary instance of the published
AllThoseEPPA/Irreducible.lean definitions. In particular, whole unary
fibres (including empty, cyclic and branching fibres) are respected.
-/
namespace GluingEPPA.Sparsening
universe u v w z t
variable {P : Type u} {F : Type v} {L : Nat → Type w} {Q : Type z}

/-- Nonconstant colourings whose true relation tuples and whole unary
fibres are monochromatic give a genuine free amalgam, over the empty
intersection. This is the constructive converse to the already checked
colour-constancy lemma for irreducibles. -/
noncomputable def freeCut_of_nonconstant_color
    (R : RelStructure L P) (out : F → P → Set P) (color : P → Q)
    (relation_color : ∀ {n} (r : L n) (xs : Fin n → P),
      R.rel r xs → ∀ i j, color (xs i) = color (xs j))
    (unary_color : ∀ f x y, y ∈ out f x → color y = color x)
    (p q : P) (hpq : color p ≠ color q) :
    UnaryFreeDecomposition R out := by
  classical
  let left : Set P := {x | color x = color p}
  let right : Set P := {x | color x ≠ color p}
  exact
    { left := left
      right := right
      left_closed := by
        intro f x y hx hy
        exact (unary_color f x y hy).trans hx
      right_closed := by
        intro f x y hx hy hh
        exact hx ((unary_color f x y hy).symm.trans hh)
      cover := by
        apply Set.eq_univ_of_forall
        intro x
        by_cases hx : color x = color p
        · exact Or.inl hx
        · exact Or.inr hx
      left_proper := by
        intro hall
        have hq : color q = color p := by
          change q ∈ left
          rw [hall]
          exact Set.mem_univ q
        exact hpq hq.symm
      right_proper := by
        intro hall
        have hp : color p ≠ color p := by
          change p ∈ right
          rw [hall]
          exact Set.mem_univ p
        exact hp rfl
      rel_local := by
        intro n r xs hr
        by_cases hn : n = 0
        · subst n
          exact Or.inl (fun i => Fin.elim0 i)
        · have hpos : 0 < n := Nat.pos_of_ne_zero hn
          let i0 : Fin n := ⟨0, hpos⟩
          by_cases h : color (xs i0) = color p
          · left
            intro i
            exact (relation_color r xs hr i i0).trans h
          · right
            intro i hh
            exact h ((relation_color r xs hr i i0).symm.trans hh)
      func_cross_empty := by
        intro f x h
        by_cases hx : color x = color p
        · exact (h (Or.inl hx)).elim
        · exact (h (Or.inr hx)).elim }

theorem constant_color_or_freeCut
    (R : RelStructure L P) (out : F → P → Set P) (color : P → Q)
    (relation_color : ∀ {n} (r : L n) (xs : Fin n → P),
      R.rel r xs → ∀ i j, color (xs i) = color (xs j))
    (unary_color : ∀ f x y, y ∈ out f x → color y = color x) :
    (∀ p q, color p = color q) ∨ Nonempty (UnaryFreeDecomposition R out) := by
  classical
  by_cases hconst : ∀ p q, color p = color q
  · exact Or.inl hconst
  · right
    simp only [not_forall] at hconst
    obtain ⟨p, q, hpq⟩ := hconst
    exact ⟨freeCut_of_nonconstant_color R out color
      relation_color unary_color p q hpq⟩

namespace ChartAtlas
variable {V : Type u} {E : Type v} {A : Type w}
variable {L : Nat → Type z} {F : Type t}
variable (G : GluingEPPA.EdgeGraph V E) (support : A → V → Prop)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (R : RelStructure L A) (out : F → A → Set A)
variable (closed : ∀ f x y s, support x s → y ∈ out f x → support y s)

/-- Every nonempty test in the ACTUAL quotient has one common lifted chart,
or admits a genuine proper free decomposition into closed induced sides.
No J-connectedness, irreducibility or extra record consistency is assumed.
This is the compact case split needed for the local-tree iteration. -/
theorem atlas_chart_or_freeCut
    (complete : ∀ s t : V, s ≠ t → ∃ e, G.Inc e s t)
    (X : Set (Vertex G support)) [Nonempty X] :
    (∃ (s : V) (chi : E → ZMod 2), ∀ q : X,
      ∃ hx : support (project G support q.val) s,
        copy G support s chi (project G support q.val) hx = q.val) ∨
      Nonempty (UnaryFreeDecomposition
        (inducedAtlas G support R X)
        (inducedOutput G support out closed X)) := by
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
  rcases constant_color_or_freeCut
      (inducedAtlas G support R X)
      (inducedOutput G support out closed X)
      (fun q : X => atlasCharge G support q.val) hrel hunary with hconst | hcut
  · rcases atlas_chart_or_closed_cut G support R out closed complete X hconst with hchart | hcut
    · exact Or.inl hchart
    · obtain ⟨e, ⟨cut⟩⟩ := hcut
      exact Or.inr ⟨cut.toFreeDecomposition⟩
  · exact Or.inr hcut

end ChartAtlas
end GluingEPPA.Sparsening
