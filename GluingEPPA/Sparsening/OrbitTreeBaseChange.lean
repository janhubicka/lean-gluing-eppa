import GluingEPPA.Sparsening.TreeBaseChange
import GluingEPPA.Sparsening.OrbitRefinedRootExact
import GluingEPPA.Sparsening.OrbitLocalTreeBounded

/-!
# Local-tree bounds with the next stage's actual root

The bounded geometric step returns trees based on the old root.
The root-chart isomorphism lets us regard the SAME targets and maps
as trees based on the new root. This closes the change-of-base
obligation before iterating the bounded step.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v t
variable {L : Nat → Type u} {F : Type t}

namespace HasTreeImage

variable {A B P : Type v}
variable {RA : RelStructure (WithJ L) A} {RB : RelStructure (WithJ L) B}
variable {outA : F → A → Set A} {outB : F → B → Set B}
variable {RP : RelStructure (WithJ L) P} {outP : F → P → Set P}

/-- Base transport changes neither the witnessing target nor its map. -/
theorem changeBase (e : Tree.ExactUnaryEmbedding RA outA RB outB)
    (he : Function.Surjective e.toFun)
    (h : HasTreeImage RB outB RP outP) :
    HasTreeImage RA outA RP outP := by
  obtain ⟨V, RV, outV, tree, hmap⟩ := h
  exact ⟨V, RV, outV, Tree.FullATree.changeBase e he tree, hmap⟩

theorem changeBase_iff (e : Tree.ExactUnaryEmbedding RA outA RB outB)
    (he : Function.Surjective e.toFun) :
    HasTreeImage RA outA RP outP ↔ HasTreeImage RB outB RP outP := by
  constructor
  · exact changeBase (e.inverse he) (e.inverse_surjective he)
  · exact changeBase e he

end HasTreeImage

open scoped Classical
noncomputable section
variable {B : Type v} [Finite B]
attribute [local instance] chartsFintype edgesFintype

/-- The exact root-chart identification preserves every local-tree claim,
including claims about empty sources and noninjective source maps. -/
theorem hasTreeImage_refinedRoot_iff
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hr : UnaryClosed out (fun b => b ∈ root))
    {P : Type v} (RP : RelStructure (WithJ L) P) (outP : F → P → Set P) :
    HasTreeImage (inducedRelations R root) (inducedUnary out root) RP outP ↔
      HasTreeImage
        (inducedRelations (relations R out root) (refinedRoot R out root hr))
        (inducedUnary (outputs R out root) (refinedRoot R out root hr)) RP outP :=
  HasTreeImage.changeBase_iff (refinedRootExact R out root hr)
    (refinedRootExact_surjective R out root hr)

/-- The bounded step in iteration-ready form: the result is based on the
NEW distinguished root rather than the previous-stage root. -/
theorem localTreeOfBoundedOldTrees_nextRoot
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hr : UnaryClosed out (fun b => b ∈ root))
    (hroot : ∀ x y, x ∈ root → y ∈ root → oldJ R x y)
    (k : Nat)
    (oldTrees : ∀ (T : Set B),
      UnaryClosed out (fun b => b ∈ T) →
      Nat.card T ≤ k →
      HasTreeImage (inducedRelations R root) (inducedUnary out root)
        (inducedRelations R T) (inducedUnary out T))
    (S : Set (Vertex R out root))
    (hS : UnaryClosed (outputs R out root) (fun q => q ∈ S))
    (hSmall : Nat.card S ≤ k + 1) :
    HasTreeImage
      (inducedRelations (relations R out root) (refinedRoot R out root hr))
      (inducedUnary (outputs R out root) (refinedRoot R out root hr))
      (ChartAtlas.inducedAtlas (graph R out root) (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root) (support R out root)
        out (closed R out root) S) := by
  exact (hasTreeImage_refinedRoot_iff R out root hr _ _).mp
    (localTreeOfBoundedOldTrees R out root hroot k oldTrees S hS hSmall)

end
end GluingEPPA.Sparsening.OrbitAtlas
