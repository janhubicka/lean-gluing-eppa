import GluingEPPA.UnorderedEdges

/-!
Exact Boolean cover over Sofia's unordered base-edge set.

The EdgeGraph endpoints are chosen representatives of unordered pairs; their
incidence is independent of the choice (unorderedGraph_inc_iff). The generic
odd-support and replay proof applies without a duplicated oriented index.
-/
namespace GluingEPPA
universe u v w z
namespace PermutationDiagramData
variable {L : Nat → Type u} {A : Type v} {U : Type w} {I : Type z}
variable {S : RelStructure L A} (D : PermutationDiagramData S U I)

variable [DecidableEq D.unorderedEdges]

/-- The label-preserving affine lift with exactly one coordinate per base edge. -/
def unorderedLiftedSymmetry (i : I) :
    (D.unorderedGraph.cover D.system).Symmetry :=
  D.unorderedGraph.liftSymmetry D.system
    (D.leftShift (D.sigma i))
    (D.edgeEquiv (D.sigma i))
    (D.unordered_incidence (D.sigma i))
    (EdgeGraph.flip
      (0 : D.unorderedEdges → ZMod 2) (D.unorderedRootEdge i))

/-- Root extension in the *unoriented* Boolean cover. -/
theorem unordered_extends_transport (i : I) {x y : A}
    (h : D.transport i x y) :
    (D.unorderedLiftedSymmetry i).map
      ((D.unorderedGraph.cover D.system).copy (Equiv.refl U, 0) x) =
    (D.unorderedGraph.cover D.system).copy (Equiv.refl U, 0) y := by
  simpa only [unorderedLiftedSymmetry] using
    (D.unorderedGraph.root_extension D.system
      (D.leftShift (D.sigma i))
      (D.edgeEquiv (D.sigma i))
      (D.unordered_incidence (D.sigma i))
      (Equiv.refl U) (D.unorderedRootEdge i) (D.unorderedRootInc i)
      x y (D.root_incoming i h))

/-- The original unordered-edge construction has induced canonical copies. -/
noncomputable def unorderedEmbedding [Fintype U] [Fintype I] :
    Embedding S ((D.unorderedGraph.cover D.system).quotientStructure S) := by
  letI : Fintype D.unorderedEdges := Fintype.ofFinite _
  exact D.unorderedGraph.coverEmbedding D.system S D.frame D.respects
    (Equiv.refl U, 0)

/-- The original unordered-edge cover has finitely many equivalence classes. -/
theorem finite_unordered_witness [Finite A] [Finite U] [Finite I] :
    Finite (D.unorderedGraph.cover D.system).Realization := by
  letI : Fintype D.unorderedEdges := Fintype.ofFinite _
  infer_instance

end PermutationDiagramData
end GluingEPPA
