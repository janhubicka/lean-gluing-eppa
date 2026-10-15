import GluingEPPA.Sparsening.OrbitLocalTreeStep
import GluingEPPA.Sparsening.ProjectionStep

/-!
# Bounded one-step local-tree preservation

A single application of the finite complete-overlap orbit refinement
raises the size of tests admitting a strict A-tree homomorphism-embedding
from at most k to at most k+1.

The chart branch embeds directly into the distinguished root. In the
free-cut branch each source side is proper, so its projected old image
has cardinality at most k, regardless of projection injectivity.
This is the numerical step of the finite sparsening induction.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v t
variable {L : Nat → Type u} {F : Type t} {B : Type v}
open scoped Classical
noncomputable section
attribute [local instance] chartsFintype edgesFintype

/-- The finite numerical induction step: old closed tests up to k vertices
suffice for ALL new closed tests up to k+1 vertices. The witness target
is a literal strict tree of full copies of the specified root. -/
theorem localTreeOfBoundedOldTrees [Finite B]
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
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
    HasTreeImage (inducedRelations R root) (inducedUnary out root)
      (ChartAtlas.inducedAtlas (graph R out root)
        (support R out root) R S)
      (ChartAtlas.inducedOutput (graph R out root)
        (support R out root) out (closed R out root) S) := by
  classical
  have hFiniteS : Finite S := inferInstance
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
      have hLeftSmall : Nat.card (projectS '' d.left) ≤ k :=
        proper_set_image_small projectS d.left d.left_proper k hSmall
      have hRightSmall : Nat.card (projectS '' d.right) ≤ k :=
        proper_set_image_small projectS d.right d.right_proper k hSmall
      obtain ⟨X, RX, outX, treeX, ⟨hx⟩⟩ :=
        oldTrees (projectS '' d.left) hClosedLeft hLeftSmall
      obtain ⟨Y, RY, outY, treeY, ⟨hy⟩⟩ :=
        oldTrees (projectS '' d.right) hClosedRight hRightSmall
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
