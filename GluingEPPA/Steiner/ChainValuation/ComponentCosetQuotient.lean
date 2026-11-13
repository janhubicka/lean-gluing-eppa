import GluingEPPA.Steiner.ChainValuation.LinkCayleyMask

/-!
# Actual masked components are precisely the earlier-subgroup cosets

The previous Cayley lemma identifies the *reachability relation* in a
single earlier block with membership in a left coset. Here we upgrade
that pointwise equivalence to a bijection between the genuine
reachability-component quotient and the collection of actual cosets.

This supplies a type-correct bridge between the quotient component
classes used by MatchingGluing and the literal Set-valued restricted
cosets used by LinkRestrictedMatching. The global finite-chain
normal form still requires assembling these bridges at all boundaries.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {G : Type u} [Group G] {E : Type v}

/-- Every masked connected component of a Cayley action is an actual
left coset. The result needs only the proved pointwise reachability
criterion and does not assume commutativity or ambient groups. -/
noncomputable def reachQuotientEquivLeftCosets
    (R : E → G → G → Prop) (M : Finset E)
    (P : Subgroup G)
    (hreach : ∀ x y : G,
      LabelReach R M x y ↔ y ∈ leftCoset P x) :
    Quotient (labelReachSetoid R M) ≃
      {C : Set G // ∃ x : G, C = leftCoset P x} := by
  let f : Quotient (labelReachSetoid R M) →
      {C : Set G // ∃ x : G, C = leftCoset P x} :=
    Quotient.lift
      (fun x : G => ⟨leftCoset P x, ⟨x, rfl⟩⟩)
      (by
        intro x y hxy
        apply Subtype.ext
        exact leftCoset_eq_of_mem ((hreach x y).mp hxy))
  apply Equiv.ofBijective f
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y hxy
    have hval := congrArg Subtype.val hxy
    change leftCoset P x = leftCoset P y at hval
    apply Quotient.sound
    apply (hreach x y).mpr
    rw [hval]
    exact self_mem_leftCoset P y
  · intro C
    obtain ⟨x, hx⟩ := C.property
    refine ⟨Quotient.mk (labelReachSetoid R M) x, ?_⟩
    apply Subtype.ext
    change leftCoset P x = C.val
    exact hx.symm

end GluingEPPA.Steiner.ChainValuation

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe w
variable {V E : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

/-- The actual M-components of a genuine earlier Cayley block K_A
are exactly its left cosets of the included group K_(M∩A).
The codomain is a subtype of *actual sets*, not abstract tokens. -/
noncomputable def restrictedBlockComponentsEquiv (M A : Proper S) :
    Quotient
      (GluingEPPA.Steiner.ChainValuation.labelReachSetoid
        (fun e => ((block S old A).matching e).Rel) M.val) ≃
    {C : Set (old A).Carrier //
      ∃ x : (old A).Carrier,
        C = GluingEPPA.Steiner.ChainValuation.leftCoset
          (L (Step.meet S M A) A Finset.inter_subset_right).incl.range x} :=
  GluingEPPA.Steiner.ChainValuation.reachQuotientEquivLeftCosets
    (fun e => ((block S old A).matching e).Rel) M.val
    (L (Step.meet S M A) A Finset.inter_subset_right).incl.range
    (restricted_block_reach_iff_coset D S old L M A)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
