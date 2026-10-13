import GluingEPPA.PermutationDiagram

/-!
A redundant *oriented* edge-indexing of the finite permutation diagram.
For each base permutation a and inverse-labelled generator i we use an edge
(a,i), with endpoints a and sigma_i⁻¹.trans(a). Each undirected edge of
the manuscript's set M occurs twice. This is a genuine (larger) Boolean
cover, not literally the same vertex set as the manuscript's B₁.
The generic parity and cover arguments allow parallel indexed edges.
-/
namespace GluingEPPA
universe u v w z

namespace PermutationDiagramData
variable {L : Nat → Type u} {A : Type v} {U : Type w} {I : Type z}
variable {S : RelStructure L A} (D : PermutationDiagramData S U I)

/-- Oriented generator occurrences serve as distinct Boolean coordinates. -/
def orientedGraph : EdgeGraph (U ≃ U) ((U ≃ U) × I) where
  left e := e.1
  right e := (D.sigma e.2).symm.trans e.1

/-- Left multiplication also permutes oriented edges. -/
def shiftEdge (g : U ≃ U) : ((U ≃ U) × I) ≃ ((U ≃ U) × I) where
  toFun e := (e.1.trans g, e.2)
  invFun e := (e.1.trans g.symm, e.2)
  left_inv := by
    intro e
    apply Prod.ext
    · apply Equiv.ext
      intro u
      simp
    · rfl
  right_inv := by
    intro e
    apply Prod.ext
    · apply Equiv.ext
      intro u
      simp
    · rfl

theorem left_shift_edge (g : U ≃ U) (e : (U ≃ U) × I) :
    D.orientedGraph.left (shiftEdge g e) =
      (D.leftShift g).perm (D.orientedGraph.left e) := rfl

theorem right_shift_edge (g : U ≃ U) (e : (U ≃ U) × I) :
    D.orientedGraph.right (shiftEdge g e) =
      (D.leftShift g).perm (D.orientedGraph.right e) := by
  apply Equiv.ext
  intro u
  rfl

/-- Explicit incidence equivariance, rather than an assumed edge action. -/
theorem shift_incidence (g : U ≃ U)
    (e : (U ≃ U) × I) (a b : U ≃ U) :
    D.orientedGraph.Inc (shiftEdge g e)
      ((D.leftShift g).perm a) ((D.leftShift g).perm b) ↔
    D.orientedGraph.Inc e a b := by
  unfold EdgeGraph.Inc
  rw [D.left_shift_edge g e, D.right_shift_edge g e]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact Or.inl ⟨(D.leftShift g).perm.injective ha,
        (D.leftShift g).perm.injective hb⟩
    · exact Or.inr ⟨(D.leftShift g).perm.injective ha,
        (D.leftShift g).perm.injective hb⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact Or.inl ⟨congrArg (D.leftShift g).perm ha,
        congrArg (D.leftShift g).perm hb⟩
    · exact Or.inr ⟨congrArg (D.leftShift g).perm ha,
        congrArg (D.leftShift g).perm hb⟩

/-- The inverse-labelled edge has endpoints 1 and sigma_i. -/
def rootEdge (i : I) : (U ≃ U) × I := (Equiv.refl U, D.inverse i)

theorem root_incidence (i : I) :
    D.orientedGraph.Inc (D.rootEdge i)
      (Equiv.refl U) ((D.leftShift (D.sigma i)).perm (Equiv.refl U)) := by
  have hright : D.orientedGraph.right (D.rootEdge i) = D.sigma i := by
    apply Equiv.ext
    intro u
    simp [orientedGraph, rootEdge, D.sigma_inverse i]
  exact Or.inl ⟨rfl, (D.root_shift i).trans hright.symm⟩

variable [DecidableEq ((U ≃ U) × I)]

/-- Affine left action on the oriented Boolean cover. -/
noncomputable def liftedSymmetry (i : I) :
    (D.orientedGraph.cover D.system).Symmetry := by
  classical
  exact D.orientedGraph.liftSymmetry D.system
    (D.leftShift (D.sigma i))
    (shiftEdge (D.sigma i))
    (D.shift_incidence (D.sigma i))
    (flip 0 (D.rootEdge i))

/-- Concrete root-extension equation for the oriented-index cover. -/
theorem extends_transport (i : I) {x y : A} (h : D.transport i x y) :
    (D.liftedSymmetry i).map
      ((D.orientedGraph.cover D.system).copy (Equiv.refl U, 0) x) =
    (D.orientedGraph.cover D.system).copy (Equiv.refl U, 0) y := by
  classical
  exact D.orientedGraph.root_extension D.system
    (D.leftShift (D.sigma i))
    (shiftEdge (D.sigma i))
    (D.shift_incidence (D.sigma i))
    (Equiv.refl U) (D.rootEdge i) (D.root_incidence i)
    x y (D.root_incoming i h)

/-- The induced root copy in this explicit finite Boolean cover. -/
noncomputable def rootEmbedding [Fintype U] [Fintype I] :
    Embedding S ((D.orientedGraph.cover D.system).quotientStructure S) := by
  classical
  exact D.orientedGraph.coverEmbedding D.system S D.frame D.respects
    (Equiv.refl U, 0)

/-- The concrete finite witness has only finitely many equivalence classes. -/
theorem finite_witness [Finite A] [Finite U] [Finite I] :
    Finite (D.orientedGraph.cover D.system).Realization := by
  classical
  infer_instance

end PermutationDiagramData
end GluingEPPA
