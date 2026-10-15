import GluingEPPA.Sparsening.OrbitRefinedRoot

/-!
# Exact identification of consecutive distinguished roots

The new zero-valuation full chart is not merely closed and J-complete.
It is EXACTLY isomorphic, as a unary-relational structure with all whole
set-valued unary fibres, to the old distinguished root.

The map is the canonical chart copy, not the generally noninjective
projection on the entire orbit refinement. This prepares transport of
literal full-A trees and the finite sparsening tower between stages.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas

universe u v w
variable {L : Nat → Type u} {F : Type w} {B : Type v}
open scoped Classical
noncomputable section
variable [Finite B]
attribute [local instance] chartsFintype edgesFintype

/-- The canonical full root chart is an exact unary-relational embedding
onto the new distinguished root, including nullary relations and the
equality of complete unary function fibres. -/
noncomputable def refinedRootExact
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hr : UnaryClosed out (fun b => b ∈ root)) :
    Tree.ExactUnaryEmbedding
      (inducedRelations R root) (inducedUnary out root)
      (inducedRelations (relations R out root) (refinedRoot R out root hr))
      (inducedUnary (outputs R out root) (refinedRoot R out root hr)) where
  toFun := fun x =>
    ⟨ChartAtlas.copy (graph R out root) (support R out root)
      (rootChart R out root hr) 0 x.val x.property,
      ⟨x.val, x.property, rfl⟩⟩
  injective := by
    intro a b hab
    exact (ChartAtlas.copy_injective
      (graph R out root) (support R out root)
      (rootChart R out root hr) 0)
      (congrArg Subtype.val hab)
  rel_iff := by
    intro n r xs
    exact (ChartAtlas.chartEmbedding
      (graph R out root) (support R out root) R
      (rootChart R out root hr) 0).rel_iff r xs
  out_eq := by
    intro f x
    ext z
    constructor
    · rintro ⟨y, hy, heq⟩
      change z.val ∈ outputs R out root f
        (ChartAtlas.copy (graph R out root) (support R out root)
          (rootChart R out root hr) 0 x.val x.property)
      rw [← congrArg Subtype.val heq]
      exact (ChartAtlas.liftOutput_copy
        (graph R out root) (support R out root)
        out (closed R out root) f
        (rootChart R out root hr) 0 x.val x.property _).mpr
        ⟨y.val, hy, rfl⟩
    · intro hz
      have hq : z.val ∈ ChartAtlas.liftOutput
          (graph R out root) (support R out root)
          out (closed R out root) f
          (ChartAtlas.copy (graph R out root) (support R out root)
            (rootChart R out root hr) 0 x.val x.property) := hz
      obtain ⟨y, hy, heq⟩ :=
        (ChartAtlas.liftOutput_copy (graph R out root)
          (support R out root) out (closed R out root) f
          (rootChart R out root hr) 0 x.val x.property z.val).mp hq
      have hyr : y ∈ root := hr f x.val y x.property hy
      refine ⟨⟨y, hyr⟩, hy, ?_⟩
      exact Subtype.ext heq

/-- The exact full-root embedding is SURJECTIVE onto the distinguished
new lifted root, giving a canonical isomorphism of the successive bases. -/
theorem refinedRootExact_surjective
    (R : RelStructure (WithJ L) B)
    (out : F → B → Set B) (root : Set B)
    (hr : UnaryClosed out (fun b => b ∈ root)) :
    Function.Surjective (refinedRootExact R out root hr).toFun := by
  rintro ⟨q, hq⟩
  obtain ⟨x, hx, heq⟩ := hq
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subtype.ext heq

end
end GluingEPPA.Sparsening.OrbitAtlas
