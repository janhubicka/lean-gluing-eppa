import GluingEPPA.OrientedAssembly

/-!
The literal unordered edge set in Sofia's base permutation diagram.

Unlike OrientedCover, each element of unorderedEdges is one unordered
pair of adjacent base permutations, with no duplicate coordinate for
opposite orientations. This module proves well-definedness of the left
action on those coordinates and prepares the exact Boolean cover.
-/
namespace GluingEPPA
universe u v w z

namespace PermutationDiagramData
variable {L : Nat → Type u} {A : Type v} {U : Type w} {I : Type z}
variable {S : RelStructure L A} (D : PermutationDiagramData S U I)

/-- Edge existence in the permutation base, without a point of A. -/
def baseAdjacent (a b : U ≃ U) : Prop :=
  ∃ i : I, ∀ x : U, b (D.sigma i x) = a x

theorem baseAdjacent_symm {a b : U ≃ U}
    (h : D.baseAdjacent a b) : D.baseAdjacent b a := by
  obtain ⟨i, hb⟩ := h
  refine ⟨D.inverse i, ?_⟩
  intro x
  rw [D.sigma_inverse i]
  simpa using (hb ((D.sigma i).symm x)).symm

theorem baseAdjacent_shift (g a b : U ≃ U) :
    D.baseAdjacent ((D.leftShift g).perm a) ((D.leftShift g).perm b) ↔
      D.baseAdjacent a b := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    intro x
    apply g.injective
    exact hi x
  · rintro ⟨i, hi⟩
    exact ⟨i, fun x => congrArg g (hi x)⟩

/-- An edge occurs once, as an unordered pair of base permutations. -/
def edgeExists (e : Sym2 (U ≃ U)) : Prop :=
  ∃ a b : U ≃ U, e = s(a, b) ∧ D.baseAdjacent a b

abbrev unorderedEdges := {e : Sym2 (U ≃ U) // D.edgeExists e}

theorem edgeExists_map (g : U ≃ U) {e : Sym2 (U ≃ U)}
    (h : D.edgeExists e) :
    D.edgeExists (Sym2.map (D.leftShift g).perm e) := by
  obtain ⟨a, b, he, hab⟩ := h
  refine ⟨(D.leftShift g).perm a, (D.leftShift g).perm b, ?_, ?_⟩
  · rw [he, Sym2.map_mk]
  · exact (D.baseAdjacent_shift g a b).mpr hab

def edgeImage (g : U ≃ U) (e : D.unorderedEdges) : D.unorderedEdges :=
  ⟨Sym2.map (D.leftShift g).perm e.1, D.edgeExists_map g e.2⟩

theorem shift_symm_shift (g a : U ≃ U) :
    (D.leftShift g.symm).perm ((D.leftShift g).perm a) = a := by
  apply Equiv.ext
  intro x
  simp [leftShift]

theorem shift_shift_symm (g a : U ≃ U) :
    (D.leftShift g).perm ((D.leftShift g.symm).perm a) = a := by
  apply Equiv.ext
  intro x
  simp [leftShift]

/-- The induced permutation of unordered edge coordinates. -/
def edgeEquiv (g : U ≃ U) : D.unorderedEdges ≃ D.unorderedEdges where
  toFun := D.edgeImage g
  invFun := D.edgeImage g.symm
  left_inv := by
    intro e
    apply Subtype.ext
    change Sym2.map (D.leftShift g.symm).perm
        (Sym2.map (D.leftShift g).perm e.1) = e.1
    induction e.1 using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.map_mk]
      rw [D.shift_symm_shift g a, D.shift_symm_shift g b]
  right_inv := by
    intro e
    apply Subtype.ext
    change Sym2.map (D.leftShift g).perm
        (Sym2.map (D.leftShift g.symm).perm e.1) = e.1
    induction e.1 using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.map_mk]
      rw [D.shift_shift_symm g a, D.shift_shift_symm g b]

/-- Choose endpoints of an unordered edge only to use the general edge
graph interface. The choice cannot affect the undirected incidence relation. -/
noncomputable def unorderedGraph : EdgeGraph (U ≃ U) D.unorderedEdges where
  left e := e.1.out.1
  right e := e.1.out.2

theorem unorderedGraph_inc_iff (e : D.unorderedEdges) (a b : U ≃ U) :
    D.unorderedGraph.Inc e a b ↔ e.1 = s(a, b) := by
  have h : e.1 = s(e.1.out.1, e.1.out.2) := e.1.out_eq.symm
  change ((a = e.1.out.1 ∧ b = e.1.out.2) ∨
     (a = e.1.out.2 ∧ b = e.1.out.1)) ↔ e.1 = s(a, b)
  conv_rhs => rw [h, Sym2.eq_iff]
  tauto

theorem unordered_incidence (g : U ≃ U)
    (e : D.unorderedEdges) (a b : U ≃ U) :
    D.unorderedGraph.Inc (D.edgeEquiv g e)
      ((D.leftShift g).perm a) ((D.leftShift g).perm b) ↔
    D.unorderedGraph.Inc e a b := by
  rw [D.unorderedGraph_inc_iff, D.unorderedGraph_inc_iff]
  change Sym2.map (D.leftShift g).perm e.1 =
      s((D.leftShift g).perm a, (D.leftShift g).perm b) ↔ e.1 = s(a, b)
  rw [← Sym2.map_mk]
  constructor
  · intro h
    exact (Sym2.map.injective (D.leftShift g).perm.injective) h
  · intro h
    rw [h]

/-- The unordered root edge indexed by a partial automorphism i. -/
def unorderedRootEdge (i : I) : D.unorderedEdges :=
  ⟨s(Equiv.refl U, D.sigma i), by
    refine ⟨Equiv.refl U, D.sigma i, rfl, ?_⟩
    refine ⟨D.inverse i, ?_⟩
    intro x
    rw [D.sigma_inverse i]
    simp⟩

theorem unorderedRootInc (i : I) :
    D.unorderedGraph.Inc (D.unorderedRootEdge i)
      (Equiv.refl U) ((D.leftShift (D.sigma i)).perm (Equiv.refl U)) := by
  rw [D.unorderedGraph_inc_iff]
  change s(Equiv.refl U, D.sigma i) =
    s(Equiv.refl U, (D.leftShift (D.sigma i)).perm (Equiv.refl U))
  rw [D.root_shift i]

instance finite_unordered [Finite U] [Finite I] : Finite D.unorderedEdges := by
  infer_instance

end PermutationDiagramData
end GluingEPPA
