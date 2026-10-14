import GluingEPPA.Sparsening.TreeProjectedFreeCut
import GluingEPPA.Sparsening.OrbitProjectionHomEmbedding
import GluingEPPA.Sparsening.AtlasRootedFreeCut

/-!
# Specialising projected free-cut gluing to the canonical orbit atlas

This is the bridge from the abstract strong tree pushout to the actual
complete-overlap quotient. For a closed test, the restricted canonical
projection preserves *entire* unary fibres. Its old side images are therefore
closed without an injectivity assumption.

The J-clique conversion accepts precisely the pointwise assertion supplied by
the atlas chart-or-rooted-free-cut theorem; it does not assume the old
projected union is a free amalgam.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v w
variable {L : Nat → Type u} {F : Type w}
variable {A B X Y : Type v}
open scoped Classical
noncomputable section
variable [Finite B]
attribute [local instance] chartsFintype edgesFintype

/-- The actual projection, restricted to a possibly empty test. -/
def testProjection (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (S : Set (Vertex R out root)) : S → B :=
  fun q => ChartAtlas.project (graph R out root)
    (support R out root) q.val

/-- On every closed test the *whole* projected unary fibre equals the
corresponding old fibre. This is stronger than being a homomorphism. -/
theorem testProjection_fibres
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (S : Set (Vertex R out root))
    (hS : UnaryClosed (outputs R out root) (fun q => q ∈ S))
    (f : F) (q : S) :
    testProjection R out root S ''
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S f q)
      = out f (testProjection R out root S q) := by
  let G := graph R out root
  let sp := support R out root
  change (fun y : S => ChartAtlas.project G sp y.val) ''
      (ChartAtlas.inducedOutput G sp out (closed R out root) S f q)
    = out f (ChartAtlas.project G sp q.val)
  ext b
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hb : ChartAtlas.project G sp y.val ∈
        ChartAtlas.project G sp ''
          ChartAtlas.liftOutput G sp out (closed R out root) f q.val :=
      ⟨y.val, hy, rfl⟩
    rw [ChartAtlas.liftOutput_projection G sp out
      (closed R out root) f q.val] at hb
    exact hb
  · intro hb
    have hmem : b ∈ ChartAtlas.project G sp ''
        ChartAtlas.liftOutput G sp out (closed R out root) f q.val := by
      rw [ChartAtlas.liftOutput_projection G sp out
        (closed R out root) f q.val]
      exact hb
    obtain ⟨y, hy, hby⟩ := hmem
    refine ⟨⟨y, hS f q.val y q.property hy⟩, hy, hby⟩

/-- The exact atlas-root conclusion gives the complete J-clique
needed by the strict-tree target gluing theorem. The overlap may
be empty, and projection need not be injective there. -/
theorem testProjection_overlap_J
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (S : Set (Vertex R out root))
    (d : UnaryFreeDecomposition
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S))
    (hJ : ∀ (p q : S), p ∈ d.left → p ∈ d.right →
      q ∈ d.left → q ∈ d.right →
      R.rel (Sum.inr (⟨(), rfl⟩ : JSymbol 2))
        (Tree.JPair (testProjection R out root S p)
          (testProjection R out root S q))) :
    Tree.IsJClique
      (inducedRelations R
        (testProjection R out root S '' (d.left ∩ d.right)))
      Set.univ := by
  intro x _ y _
  obtain ⟨p, hp, hpx⟩ := x.property
  obtain ⟨q, hq, hqy⟩ := y.property
  change R.rel (Sum.inr (⟨(), rfl⟩ : JSymbol 2))
    (Tree.JPair x.val y.val)
  rw [← hpx, ← hqy]
  exact hJ p q hp.1 hp.2 hq.1 hq.2

/-- Concrete canonical-atlas version of the projected separator-root
gluing theorem. The only extra geometric hypothesis is that the
projected actual overlap is J-complete; complete unary fibres and
closed old images are derived, not assumed. -/
theorem glueProjectedAtlasCut
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (RA : RelStructure (WithJ L) A) (outA : F → A → Set A)
    (S : Set (Vertex R out root))
    (hS : UnaryClosed (outputs R out root) (fun q => q ∈ S))
    (d : UnaryFreeDecomposition
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S))
    (hJ : Tree.IsJClique
      (inducedRelations R
        (testProjection R out root S '' (d.left ∩ d.right)))
      Set.univ)
    (RX : RelStructure (WithJ L) X) (outX : F → X → Set X)
    (RY : RelStructure (WithJ L) Y) (outY : F → Y → Set Y)
    (treeX : Tree.FullATree RA outA RX outX)
    (treeY : Tree.FullATree RA outA RY outY)
    (hx : Tree.UnaryHomEmbedding
      (inducedRelations R (testProjection R out root S '' d.left))
      (inducedUnary out (testProjection R out root S '' d.left)) RX outX)
    (hy : Tree.UnaryHomEmbedding
      (inducedRelations R (testProjection R out root S '' d.right))
      (inducedUnary out (testProjection R out root S '' d.right)) RY outY) :
    ∃ (V : Type v) (RV : RelStructure (WithJ L) V)
      (outV : F → V → Set V),
      Tree.FullATree RA outA RV outV ∧
      Nonempty (Tree.UnaryHomEmbedding
        (ChartAtlas.inducedAtlas (graph R out root)
          (support R out root) R S)
        (ChartAtlas.inducedOutput (graph R out root)
          (support R out root) out (closed R out root) S) RV outV) := by
  let p : Tree.UnaryHomEmbedding
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S)
      R out :=
    (projectionHomEmbedding R out root).restrictClosed S hS
  exact Tree.FullATree.glueProjectedFreeCut
    (ChartAtlas.inducedAtlas (graph R out root)
      (support R out root) R S)
    (ChartAtlas.inducedOutput (graph R out root)
      (support R out root) out (closed R out root) S)
    R out RA outA d p
    (testProjection_fibres R out root S hS) hJ
    RX outX RY outY treeX treeY hx hy

end
end GluingEPPA.Sparsening.OrbitAtlas
