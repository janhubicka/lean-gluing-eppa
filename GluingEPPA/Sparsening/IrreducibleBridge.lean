import GluingEPPA.Sparsening.OrbitEndpoint
import GluingEPPA.Sparsening.AtlasSeparator

/-!
# Irreducibility and faithfulness for the gluing atlas

This is a *compatibility port* of the definitions and the
\`irreducible_subset_one_side\` principle from
\`shulda/lean_all_those_eppa_classes\`, specifically
\`AllThoseEPPA/Irreducible.lean\`. We keep the verified semantics:
irreducible means admitting no free decomposition into two proper closed
induced sides, relations cannot cross the exclusive sides, and unary
set-valued functions must preserve the whole fibre.

The direct import is deferred because the published AllThoseEPPA dependency
pins Lean v4.34.1 while this repository pins v4.35.0-rc3. In particular this
file does not pretend that its type names are definitionally the external ones.
The proof consumes the *actual* atlas separator, with no assumed sparseness.
-/
namespace GluingEPPA.Sparsening

universe u v w z
variable {P : Type u} {F : Type v} {L : Nat → Type w}

/-- The unary instance of AllThoseEPPA.Structure.FreeDecomposition.
Its function-crossing condition is automatic because each input is unary
and the two sides cover every vertex. -/
structure UnaryFreeDecomposition (R : RelStructure L P)
    (out : F → P → Set P) where
  left : Set P
  right : Set P
  left_closed : UnaryClosed out (fun p => p ∈ left)
  right_closed : UnaryClosed out (fun p => p ∈ right)
  cover : left ∪ right = Set.univ
  left_proper : left ≠ Set.univ
  right_proper : right ≠ Set.univ
  rel_local : ∀ {n} (r : L n) (xs : Fin n → P), R.rel r xs →
    (∀ i, xs i ∈ left) ∨ (∀ i, xs i ∈ right)
  func_cross_empty : ∀ f x, ¬ (x ∈ left ∨ x ∈ right) → out f x = ∅

/-- Irreducibility is absence of any free decomposition, as in
AllThoseEPPA.Structure.IsIrreducible. -/
def IsIrreducible (R : RelStructure L P) (out : F → P → Set P) : Prop :=
  IsEmpty (UnaryFreeDecomposition R out)

/-- The checked exterior-coordinate closed cut is a genuine free
decomposition in the survey's sense, not a weaker graph separation. -/
def ClosedCut.toFreeDecomposition {R : RelStructure L P}
    {out : F → P → Set P} {root : P → Prop}
    (cut : ClosedCut R out root) : UnaryFreeDecomposition R out where
  left := {p | cut.left p}
  right := {p | cut.right p}
  left_closed := cut.left_closed
  right_closed := cut.right_closed
  cover := by
    apply Set.eq_univ_of_forall
    intro p
    exact cut.cover p
  left_proper := by
    obtain ⟨p, hp⟩ := cut.proper_left
    intro h
    exact hp (by rw [h]; exact Set.mem_univ p)
  right_proper := by
    obtain ⟨p, hp⟩ := cut.proper_right
    intro h
    exact hp (by rw [h]; exact Set.mem_univ p)
  rel_local := cut.tuple_side
  func_cross_empty := by
    intro f p h
    exact (h (cut.cover p)).elim

theorem no_closed_cut_of_irreducible (R : RelStructure L P)
    (out : F → P → Set P) (hirr : IsIrreducible R out)
    {root : P → Prop} (cut : ClosedCut R out root) : False :=
  hirr.false cut.toFreeDecomposition

/-- An irreducible unary relational structure is monochromatic whenever
true relation tuples and complete unary fibres are monochromatic.
The zero-ary case is included: no coordinate can cross either side. -/
theorem color_constant_of_irreducible {Q : Type z}
    (R : RelStructure L P) (out : F → P → Set P)
    (color : P → Q)
    (relation_color : ∀ {n} (r : L n) (xs : Fin n → P),
      R.rel r xs → ∀ i j, color (xs i) = color (xs j))
    (unary_color : ∀ f x y, y ∈ out f x → color y = color x)
    (hirr : IsIrreducible R out) (p q : P) : color p = color q := by
  classical
  by_contra hpq
  let left : Set P := {x | color x = color p}
  let right : Set P := {x | color x ≠ color p}
  let d : UnaryFreeDecomposition R out :=
    { left := left
      right := right
      left_closed := by
        intro f x y hx hy
        exact (unary_color f x y hy).trans hx
      right_closed := by
        intro f x y hx hy h
        exact hx ((unary_color f x y hy).symm.trans h)
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
            intro i hi
            exact h ((relation_color r xs hr i i0).symm.trans hi)
      func_cross_empty := by
        intro f x hx
        have hc : x ∈ left ∪ right := by
          rw [show left ∪ right = Set.univ from
            (by
              apply Set.eq_univ_of_forall
              intro z
              by_cases hz : color z = color p
              · exact Or.inl hz
              · exact Or.inr hz)]
          exact Set.mem_univ x
        exact (hx hc).elim }
  exact hirr.false d

end GluingEPPA.Sparsening
