import GluingEPPA.Sparsening.OrbitFiniteTower
import GluingEPPA.Sparsening.ForgetJ

/-!
# The geometric conclusions in the original language

Forgetting J preserves the actual maps, their complete unary fibres,
and the strict tree amalgamations. Every positive refinement is faithful
also for irreducible tests in the reduct. This completes the geometric
part of the finite tower, but does not supply its EPPA extension family.
-/

namespace GluingEPPA.Sparsening.OrbitAtlas.FiniteRooted

universe u t
variable {L : Nat → Type u} {F : Type t}
open scoped Classical
noncomputable section
attribute [local instance] chartsFintype edgesFintype
variable (C : FiniteRooted L F)

/-- The same composite projection is a homomorphism-embedding in L. -/
def reductProjection (n : Nat) :
    Tree.UnaryHomEmbedding (forgetJRelations (C.tower n).rel) (C.tower n).out
      (forgetJRelations C.rel) C.out :=
  (C.projectToBase n).forgetJ

/-- Root identification is unaffected by forgetting the auxiliary relation. -/
theorem reductProjection_root (n : Nat) (a : C.root) :
    (C.reductProjection n).toFun ((C.rootEmbedding n).toFun a).val = a.val :=
  C.projectToBase_root n a

/-- The finite local target uses full copies of the original L-root,
not merely the auxiliary expansion. Both the tree and map are reduced. -/
theorem tower_reduct_local_finite_target (n : Nat)
    (S : Set (C.tower n).Carrier)
    (hS : UnaryClosed (C.tower n).out (fun x => x ∈ S))
    (hSmall : Nat.card S ≤ n) :
    ∃ (V : Type _) (RV : RelStructure L V) (outV : F → V → Set V),
      Finite V ∧ Tree.FullATree (forgetJRelations C.rootRelations)
        C.rootOutputs RV outV ∧
      Nonempty (Tree.UnaryHomEmbedding
        (inducedRelations (forgetJRelations (C.tower n).rel) S)
        (inducedUnary (C.tower n).out S) RV outV) := by
  obtain ⟨V, RV, outV, hV, tree, ⟨hmap⟩⟩ := C.tower_local_finite_target n S hS hSmall
  exact ⟨V, forgetJRelations RV, outV, hV, tree.forgetJ, ⟨hmap.forgetJ⟩⟩

/-- Every irreducible closed test of one refined reduct can be moved into
its distinguished root by an automorphism of the reduct, including the
empty test. The moving automorphism comes from the expanded construction. -/
theorem refine_reduct_faithful (S : Set C.refine.Carrier)
    (hS : UnaryClosed C.refine.out (fun x => x ∈ S))
    (hirr : IsIrreducible (inducedRelations (forgetJRelations C.refine.rel) S)
      (inducedUnary C.refine.out S)) :
    ∃ g : Aut (forgetJRelations C.refine.rel) C.refine.out,
      ∀ x, x ∈ S → g.perm x ∈ C.refine.root := by
  by_cases hne : Nonempty S
  · have hi : IsIrreducible (inducedRelations C.refine.rel S)
        (inducedUnary C.refine.out S) :=
      irreducible_expand_J (inducedRelations C.refine.rel S)
        (inducedUnary C.refine.out S) hirr
    obtain ⟨g, hg⟩ := @irreducible_move_into_root _ _ _ C.rel C.out C.root
      C.finite C.root_closed S hne hS hi
    exact ⟨g.forgetJ, hg⟩
  · refine ⟨Aut.refl, ?_⟩
    intro x hx
    exact (hne ⟨⟨x, hx⟩⟩).elim

/-- Faithfulness requires a positive number of refinements, independently
of the chosen local bound. This is why the manuscript uses max(1,n). -/
theorem tower_reduct_faithful (n : Nat) (hn : 0 < n)
    (S : Set (C.tower n).Carrier)
    (hS : UnaryClosed (C.tower n).out (fun x => x ∈ S))
    (hirr : IsIrreducible
      (inducedRelations (forgetJRelations (C.tower n).rel) S)
      (inducedUnary (C.tower n).out S)) :
    ∃ g : Aut (forgetJRelations (C.tower n).rel) (C.tower n).out,
      ∀ x, x ∈ S → g.perm x ∈ (C.tower n).root := by
  cases n with
  | zero => omega
  | succ n => exact (C.tower n).refine_reduct_faithful S hS hirr

end
end GluingEPPA.Sparsening.OrbitAtlas.FiniteRooted
