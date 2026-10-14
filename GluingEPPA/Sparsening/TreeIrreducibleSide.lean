import GluingEPPA.Sparsening.IrreducibleBridge

/-!
# Irreducibles of a free amalgam lie wholly on one side

A short unary-language port of the already verified
AllThoseEPPA.Structure.irreducible_subset_one_side.

The induced closed substructure has genuinely complete unary fibres; its
irreducibility prevents it meeting both exclusive sides of a free cut.
This is the semantic induction step behind full-copy containment in a
recursive tree amalgam, not a new graph-connectivity assumption.
-/
namespace GluingEPPA.Sparsening
universe u v w t
variable {L : Nat → Type u} {P : Type v} {F : Type w}

def inducedRelations (R : RelStructure L P) (S : Set P) :
    RelStructure L S where
  rel r xs := R.rel r (fun i => (xs i).val)

def inducedUnary (out : F → P → Set P) (S : Set P) :
    F → S → Set S :=
  fun f x => {y | y.val ∈ out f x.val}

/-- A closed subset retains its entire original unary fibre. -/
theorem inducedUnary_full (out : F → P → Set P) (S : Set P)
    (hS : UnaryClosed out (fun p => p ∈ S))
    (f : F) (x : S) :
    Subtype.val '' inducedUnary out S f x = out f x.val := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hy
    exact ⟨⟨z, hS f x.val z x.property hy⟩, hy, rfl⟩

/-- A closed induced irreducible substructure of a genuine free amalgam
is wholly on one side. Includes arbitrary relation arities (also zero)
and complete set-valued unary functions. -/
theorem irreducible_subset_one_side
    (R : RelStructure L P) (out : F → P → Set P)
    (d : UnaryFreeDecomposition R out)
    (S : Set P) (hS : UnaryClosed out (fun p => p ∈ S))
    (hirr : IsIrreducible (inducedRelations R S) (inducedUnary out S)) :
    S ⊆ d.left ∨ S ⊆ d.right := by
  classical
  by_contra h
  have hnl : ¬ S ⊆ d.left := by
    intro hl
    exact h (Or.inl hl)
  have hnr : ¬ S ⊆ d.right := by
    intro hr
    exact h (Or.inr hr)
  let leftS : Set S := {p | p.val ∈ d.left}
  let rightS : Set S := {p | p.val ∈ d.right}
  have hlclosed : UnaryClosed (inducedUnary out S)
      (fun p => p ∈ leftS) := by
    intro f x y hx hy
    exact d.left_closed f x.val y.val hx hy
  have hrclosed : UnaryClosed (inducedUnary out S)
      (fun p => p ∈ rightS) := by
    intro f x y hx hy
    exact d.right_closed f x.val y.val hx hy
  have hcover : leftS ∪ rightS = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    have hp : p.val ∈ d.left ∪ d.right := by
      rw [d.cover]
      exact Set.mem_univ p.val
    exact hp
  have hleft : leftS ≠ Set.univ := by
    obtain ⟨x, hxS, hxL⟩ := Set.not_subset.mp hnl
    intro hall
    have hx : (⟨x, hxS⟩ : S) ∈ leftS := by
      rw [hall]
      exact Set.mem_univ _
    exact hxL hx
  have hright : rightS ≠ Set.univ := by
    obtain ⟨x, hxS, hxR⟩ := Set.not_subset.mp hnr
    intro hall
    have hx : (⟨x, hxS⟩ : S) ∈ rightS := by
      rw [hall]
      exact Set.mem_univ _
    exact hxR hx
  let dec : UnaryFreeDecomposition
      (inducedRelations R S) (inducedUnary out S) :=
    { left := leftS
      right := rightS
      left_closed := hlclosed
      right_closed := hrclosed
      cover := hcover
      left_proper := hleft
      right_proper := hright
      rel_local := by
        intro n r xs hrel
        have hrel_old : R.rel r (fun i => (xs i).val) := hrel
        rcases d.rel_local r (fun i => (xs i).val) hrel_old with hl | hr
        · exact Or.inl hl
        · exact Or.inr hr
      func_cross_empty := by
        intro f x hx
        have hc : x ∈ leftS ∪ rightS := by
          rw [hcover]
          exact Set.mem_univ x
        exact (hx hc).elim }
  exact hirr.false dec

end GluingEPPA.Sparsening
