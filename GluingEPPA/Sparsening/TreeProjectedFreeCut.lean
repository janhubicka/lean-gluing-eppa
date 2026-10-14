import GluingEPPA.Sparsening.TreeProjectedRootAssembly
import GluingEPPA.Sparsening.ProjectionStep

/-!
# Projected upstairs free cuts already have the correct closed old images

The source free cut has actual closed sides and intersection. Equality of
whole unary fibres under the projection therefore makes all three old
images closed. This is independent of projection injectivity, and needs
no assumption that the old union is a free amalgam.

Combined with the preceding abstract J-root tree gluing, the only
extra input is completeness of the actual projected common root J.
This formulation is directly adapted to the canonical Boolean atlas.
-/

namespace GluingEPPA.Sparsening.Tree

universe u v t
variable {L : Nat → Type u} {F : Type t}
variable {P B A X Y : Type v}

/-- The actual source free cut automatically has closed projected side
images and a closed projected overlap when the map has exactly
surjective whole unary fibres. Its image need not be a free cut. -/
theorem FullATree.glueProjectedFreeCut
    (RP : RelStructure (WithJ L) P) (outP : F → P → Set P)
    (RB : RelStructure (WithJ L) B) (outB : F → B → Set B)
    (RA : RelStructure (WithJ L) A) (outA : F → A → Set A)
    (d : UnaryFreeDecomposition RP outP)
    (p : UnaryHomEmbedding RP outP RB outB)
    (pFibres : ∀ f z, p.toFun '' outP f z = outB f (p.toFun z))
    (hJ : IsJClique
      (inducedRelations RB (p.toFun '' (d.left ∩ d.right))) Set.univ)
    (RX : RelStructure (WithJ L) X) (outX : F → X → Set X)
    (RY : RelStructure (WithJ L) Y) (outY : F → Y → Set Y)
    (treeX : FullATree RA outA RX outX)
    (treeY : FullATree RA outA RY outY)
    (hx : UnaryHomEmbedding
      (inducedRelations RB (p.toFun '' d.left))
      (inducedUnary outB (p.toFun '' d.left)) RX outX)
    (hy : UnaryHomEmbedding
      (inducedRelations RB (p.toFun '' d.right))
      (inducedUnary outB (p.toFun '' d.right)) RY outY) :
    ∃ (V : Type v) (RV : RelStructure (WithJ L) V)
      (outV : F → V → Set V),
      FullATree RA outA RV outV ∧
      Nonempty (UnaryHomEmbedding RP outP RV outV) := by
  have hl : UnaryClosed outB
      (fun b => b ∈ p.toFun '' d.left) :=
    unary_image_closed outP outB (fun z => z ∈ d.left)
      d.left_closed p.toFun pFibres
  have hr : UnaryClosed outB
      (fun b => b ∈ p.toFun '' d.right) :=
    unary_image_closed outP outB (fun z => z ∈ d.right)
      d.right_closed p.toFun pFibres
  have hz : UnaryClosed outP
      (fun z => z ∈ d.left ∩ d.right) := by
    intro f z w hz hw
    exact ⟨d.left_closed f z w hz.1 hw,
      d.right_closed f z w hz.2 hw⟩
  have hzB : UnaryClosed outB
      (fun b => b ∈ p.toFun '' (d.left ∩ d.right)) :=
    unary_image_closed outP outB
      (fun z => z ∈ d.left ∩ d.right) hz p.toFun pFibres
  have hsubsetL : p.toFun '' (d.left ∩ d.right) ⊆
      p.toFun '' d.left := by
    rintro b ⟨z, hz, rfl⟩
    exact ⟨z, hz.1, rfl⟩
  have hsubsetR : p.toFun '' (d.left ∩ d.right) ⊆
      p.toFun '' d.right := by
    rintro b ⟨z, hz, rfl⟩
    exact ⟨z, hz.2, rfl⟩
  exact FullATree.glueProjectedRoot
    RP outP RB outB RA outA d p
    (p.toFun '' d.left) (p.toFun '' d.right)
    (p.toFun '' (d.left ∩ d.right))
    hl hr hzB
    (fun z => ⟨z.val, z.property, rfl⟩)
    (fun z => ⟨z.val, z.property, rfl⟩)
    hsubsetL hsubsetR
    (fun z hzl hzr => ⟨z, ⟨hzl, hzr⟩, rfl⟩)
    hJ RX outX RY outY treeX treeY hx hy

end GluingEPPA.Sparsening.Tree
