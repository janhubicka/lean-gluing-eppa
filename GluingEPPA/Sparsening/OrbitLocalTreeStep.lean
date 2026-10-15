import GluingEPPA.Sparsening.OrbitChartExact

/-!
# The one-step local tree argument, separated from cardinal arithmetic

Given strict full-A target trees for every closed old test, the canonical
complete-overlap refinement again admits a strict full-A target tree for every
closed upstairs test. Both chart and free-cut branches use the *actual*
canonical atlas: the chart branch embeds exactly into the distinguished old
root; the cut branch glues the old projected side targets across the true
upstairs free decomposition.

The size-restricted finite induction still needs the proper-side
cardinality lemma. This result proves the entire non-numerical step without
assuming injectivity of the atlas projection or any old free decomposition.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v t
variable {L : Nat → Type u} {F : Type t}
variable {B : Type v}
open scoped Classical
noncomputable section
attribute [local instance] chartsFintype edgesFintype

/-- Reusable packaging of a homomorphism-embedding into a strict tree of
full copies of the *specified* base structure. Source and base may have
distinct vertex types of the same universe level. -/
def HasTreeImage {A P : Type v}
    (RA : RelStructure (WithJ L) A) (outA : F → A → Set A)
    (RP : RelStructure (WithJ L) P) (outP : F → P → Set P) : Prop :=
  ∃ (V : Type v) (RV : RelStructure (WithJ L) V)
      (outV : F → V → Set V),
      Tree.FullATree RA outA RV outV ∧
      Nonempty (Tree.UnaryHomEmbedding RP outP RV outV)

/-- An exact map into the distinguished root provides a one-node full-root
tree target, without a separate image factorisation theorem. -/
theorem chartHasTreeImage [Finite B]
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (S : Set (Vertex R out root))
    (hS : UnaryClosed (outputs R out root) (fun q => q ∈ S))
    (s : Chart R out root) (chi : Edges R out root → ZMod 2)
    (hchart : ∀ q : S, ∃ hx : support R out root
        (testProjection R out root S q) s,
      ChartAtlas.copy (graph R out root) (support R out root)
        s chi (testProjection R out root S q) hx = q.val) :
    HasTreeImage (inducedRelations R root) (inducedUnary out root)
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S) := by
  obtain ⟨e⟩ := exists_chartTestRootExact R out root s chi S hS hchart
  exact ⟨root, inducedRelations R root, inducedUnary out root,
    Tree.FullATree.singleton (inducedRelations R root)
      (inducedUnary out root), ⟨e.toHomEmbedding⟩⟩

/-- The entire geometric one-step argument. The assumption that *all*
closed old tests have tree images will later be weakened to old tests
of size at most k via the strictly smaller projected free-cut sides. -/
theorem localTreeOfOldTrees [Finite B]
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hroot : ∀ x y, x ∈ root → y ∈ root → oldJ R x y)
    (oldTrees : ∀ (T : Set B),
      UnaryClosed out (fun b => b ∈ T) →
      HasTreeImage (inducedRelations R root) (inducedUnary out root)
        (inducedRelations R T) (inducedUnary out T))
    (S : Set (Vertex R out root))
    (hS : UnaryClosed (outputs R out root) (fun q => q ∈ S)) :
    HasTreeImage (inducedRelations R root) (inducedUnary out root)
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S) := by
  classical
  by_cases hne : Nonempty S
  · letI : Nonempty S := hne
    rcases chart_or_projected_Jclique R out root hroot S with
      ⟨s, chi, hchart⟩ | ⟨d, hJ⟩
    · exact chartHasTreeImage R out root S hS s chi hchart
    · let outS := ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S
      let projectS := testProjection R out root S
      have hF : ∀ f q, projectS '' outS f q = out f (projectS q) :=
        testProjection_fibres R out root S hS
      have hClosedLeft :
          UnaryClosed out (fun b => b ∈ projectS '' d.left) :=
        unary_image_closed outS out (fun z : S => z ∈ d.left)
          d.left_closed projectS hF
      have hClosedRight :
          UnaryClosed out (fun b => b ∈ projectS '' d.right) :=
        unary_image_closed outS out (fun z : S => z ∈ d.right)
          d.right_closed projectS hF
      obtain ⟨X, RX, outX, treeX, ⟨hx⟩⟩ :=
        oldTrees (projectS '' d.left) hClosedLeft
      obtain ⟨Y, RY, outY, treeY, ⟨hy⟩⟩ :=
        oldTrees (projectS '' d.right) hClosedRight
      exact glueProjectedAtlasCut R out root
        (inducedRelations R root) (inducedUnary out root)
        S hS d hJ RX outX RY outY treeX treeY hx hy
  · let s := emptyChart R out root
    let chi : Edges R out root → ZMod 2 := 0
    have hchart : ∀ q : S, ∃ hx : support R out root
        (testProjection R out root S q) s,
      ChartAtlas.copy (graph R out root) (support R out root)
        s chi (testProjection R out root S q) hx = q.val := by
      intro q
      exact (hne ⟨q⟩).elim
    exact chartHasTreeImage R out root S hS s chi hchart

end
end GluingEPPA.Sparsening.OrbitAtlas
