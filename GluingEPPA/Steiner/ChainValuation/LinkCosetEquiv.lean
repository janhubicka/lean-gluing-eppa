import GluingEPPA.Steiner.ChainValuation.LinkCosetEdgeEquiv

/-!
# The literal smaller-mask Cayley group is a whole old-block coset

For the actual earlier Link inclusion K_(M ∩ A) → K_A, left
translation yields a bijection from the entire smaller-stage group
onto the selected M-component of K_A. This bijection preserves and
reflects genuine M-coloured Cayley edges.

No ambient K_S, normality, or commutativity is assumed. This is the
single-block chart needed by the finite-chain normalization induction.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- The left-translated real earlier Link inclusion gives an exact
bijection of the smaller-mask group with its full M-component coset. -/
noncomputable def restrictedBlock_cosetEquiv
    (M A : Proper S) (g : (old A).Carrier) :
    (old (Step.meet S M A)).Carrier ≃
      {y : (old A).Carrier //
        y ∈ leftCoset
          (L (Step.meet S M A) A Finset.inter_subset_right).incl.range g} := by
  let T : Proper S := Step.meet S M A
  let i : (old T).Carrier →* (old A).Carrier :=
    (L T A Finset.inter_subset_right).incl
  have hi : Function.Injective i :=
    Link.injective D (old T) (old A)
      Finset.inter_subset_right (L T A Finset.inter_subset_right)
  let F : (old T).Carrier →
      {y : (old A).Carrier // y ∈ leftCoset i.range g} :=
    fun x => ⟨g * i x, by
      change g⁻¹ * (g * i x) ∈ i.range
      simpa only [inv_mul_cancel_left] using
        (show i x ∈ i.range from ⟨x, rfl⟩)⟩
  apply Equiv.ofBijective F
  constructor
  · intro x y h
    apply hi
    apply mul_left_cancel (a := g)
    exact congrArg Subtype.val h
  · rintro ⟨y, hy⟩
    change g⁻¹ * y ∈ i.range at hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, Subtype.ext ?_⟩
    change g * i x = y
    rw [hx]
    simp

/-- At all letters of M, the explicit coset bijection both
preserves and reflects the genuine labelled-edge relation. This
includes letters of M absent from A, when both edge relations are empty. -/
theorem restrictedBlock_cosetEquiv_edge_iff
    (M A : Proper S) (g : (old A).Carrier)
    (e : E) (heM : e ∈ M.val)
    (x y : (old (Step.meet S M A)).Carrier) :
    ((block S old (Step.meet S M A)).matching e).Rel x y ↔
    ((block S old A).matching e).Rel
      ((restrictedBlock_cosetEquiv D S old L M A g x).val)
      ((restrictedBlock_cosetEquiv D S old L M A g y).val) := by
  change
    ((block S old (Step.meet S M A)).matching e).Rel x y ↔
    ((block S old A).matching e).Rel
      (g * (L (Step.meet S M A) A Finset.inter_subset_right).incl x)
      (g * (L (Step.meet S M A) A Finset.inter_subset_right).incl y)
  exact restrictedBlock_translation_edge_iff
    D S old L M A g e heM x y

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
