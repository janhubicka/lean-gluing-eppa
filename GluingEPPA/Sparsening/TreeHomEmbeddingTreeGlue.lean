import GluingEPPA.Sparsening.TreeHomEmbeddingGlue

/-!
# Attach two homomorphism-embedding targets along an external J-root

The attachment is specified by an EXACT common root in the target trees.
A complete J-relation on that abstract root transfers to both embedded
ranges; the strict A-tree constructor then glues those targets.
Independently, the checked upstairs free-cut universal map assembles the
source homomorphism-embedding.

Crucially, the source root need not be an exact copy of the abstract
target root, and the image of the upstairs free cut need not itself be
a free cut. This formulation is designed for the projection of the
actual Boolean-atlas separator root.
-/

namespace GluingEPPA.Sparsening.Tree

universe u v t
variable {L : Nat → Type u} {F : Type t}
variable {P I A X Y : Type v}

/-- An exact embedding preserves completeness of the auxiliary J on its
entire source; no nonempty-root assumption is required. -/
theorem ExactUnaryEmbedding.range_JClique
    {RI : RelStructure (WithJ L) I}
    {RX : RelStructure (WithJ L) X}
    {outI : F → I → Set I}
    {outX : F → X → Set X}
    (e : ExactUnaryEmbedding RI outI RX outX)
    (hJ : IsJClique RI Set.univ) :
    IsJClique RX (Set.range e.toFun) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hj : RI.rel (Sum.inr (⟨(), rfl⟩ : JSymbol 2)) (JPair a b) :=
    hJ a (Set.mem_univ _) b (Set.mem_univ _)
  have hjx : RX.rel (Sum.inr (⟨(), rfl⟩ : JSymbol 2))
      (fun i => e.toFun (JPair a b i)) :=
    (e.rel_iff (Sum.inr (⟨(), rfl⟩ : JSymbol 2)) (JPair a b)).mpr hj
  have heq : (fun i : Fin 2 => e.toFun (JPair a b i)) =
      JPair (e.toFun a) (e.toFun b) := by
    funext i
    fin_cases i <;> rfl
  simpa only [heq] using hjx

/-- Simultaneously construct a strict full-A target tree and a
homomorphism-embedding of an upstairs free-amalgam source into it.
The common root I is an EXTERNAL closed J-clique, not necessarily an
induced substructure of the source. Its two exact target images must
represent the maps of the actual source overlap.

This is the algebraic gluing interface for the projected-separator
local-tree induction. The atlas-specific root/image construction and
the size induction remain separate obligations. -/
theorem FullATree.glueHomEmbedding
    (RP : RelStructure (WithJ L) P) (outP : F → P → Set P)
    (d : UnaryFreeDecomposition RP outP)
    (RI : RelStructure (WithJ L) I) (outI : F → I → Set I)
    (RA : RelStructure (WithJ L) A) (outA : F → A → Set A)
    (RX : RelStructure (WithJ L) X) (outX : F → X → Set X)
    (RY : RelStructure (WithJ L) Y) (outY : F → Y → Set Y)
    (treeX : FullATree RA outA RX outX)
    (treeY : FullATree RA outA RY outY)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (hJ : IsJClique RI Set.univ)
    (l : UnaryHomEmbedding
      (inducedRelations RP d.left) (inducedUnary outP d.left) RX outX)
    (r : UnaryHomEmbedding
      (inducedRelations RP d.right) (inducedUnary outP d.right) RY outY)
    (hroot : ∀ (z : P) (hzL : z ∈ d.left) (hzR : z ∈ d.right),
      ∃ i : I, l.toFun ⟨z, hzL⟩ = ef.toFun i ∧
        r.toFun ⟨z, hzR⟩ = eg.toFun i) :
    FullATree RA outA
      (pushoutRelations ef.toFun eg.toFun RX RY)
      (pushoutOutput ef.toFun eg.toFun outX outY) ∧
    Nonempty (UnaryHomEmbedding RP outP
      (pushoutRelations ef.toFun eg.toFun RX RY)
      (pushoutOutput ef.toFun eg.toFun outX outY)) := by
  refine ⟨FullATree.glue_JRoots RI outI RA outA RX outX RY outY
      treeX treeY ef eg
      (ef.range_JClique hJ) (eg.range_JClique hJ), ?_⟩
  exact ⟨unaryHomEmbedding_glueFreeCut d ef eg l r hroot⟩

end GluingEPPA.Sparsening.Tree
