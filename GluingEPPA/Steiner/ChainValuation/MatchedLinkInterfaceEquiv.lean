import GluingEPPA.Steiner.ChainValuation.MatchedLinkInterfaceMask

/-!
# Exact small-stage coordinates for a real matched Link interface

The interface of two matched M-cosets in consecutive earlier
Cayley blocks is not merely an abstract subgroup coset: its
points are bijectively parameterized by the actual earlier group
K_(M ∩ A ∩ B), translated in K_(A ∩ B) by the chosen attachment
parameter k. Thus the normalized chain has a concrete interface
carrier, with no appeal to an unconstructed full-stage group.

This identifies the *set-level* interface. Compatibility of its
left/right inclusions with normalized block charts is the separate
noncommutative boundary-square lemma (PR #118).
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

/-- The complete interface of two matched Link cosets is equivalent
to the actual smaller triple-mask group, by a left translation of the
literal earlier Link embedding. -/
noncomputable def matchedLinkCoset_interface_equiv
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier) :
    (old (Step.meet S M (common S A B))).Carrier ≃
      (matchedLinkCosetRestriction D S old L M A B h k).Interface := by
  let I : Proper S := common S A B
  let T : Proper S := Step.meet S M I
  let i : (old T).Carrier →* (old I).Carrier :=
    (L T I Finset.inter_subset_right).incl
  have hi : Function.Injective i :=
    Link.injective D (old T) (old I)
      Finset.inter_subset_right (L T I Finset.inter_subset_right)
  let W := matchedLinkCosetRestriction D S old L M A B h k
  let F : (old T).Carrier → W.Interface :=
    fun t => ⟨k * i t, by
      exact (matchedLinkCoset_interface_exact_iff
        D S old L M A B h k (k * i t)).mpr
        (by
          change k⁻¹ * (k * i t) ∈ i.range
          simpa only [inv_mul_cancel_left] using
            (show i t ∈ i.range from ⟨t, rfl⟩))⟩
  apply Equiv.ofBijective F
  constructor
  · intro x y he
    apply hi
    apply mul_left_cancel (a := k)
    exact congrArg Subtype.val he
  · rintro ⟨z, hz⟩
    have hz' : z ∈ leftCoset i.range k :=
      (matchedLinkCoset_interface_exact_iff
        D S old L M A B h k z).mp hz
    change k⁻¹ * z ∈ i.range at hz'
    obtain ⟨t, ht⟩ := hz'
    refine ⟨t, Subtype.ext ?_⟩
    change k * i t = z
    rw [ht]
    simp

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
