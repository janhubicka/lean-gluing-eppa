import GluingEPPA.Steiner.ChainValuation.CayleyMaskReach
import GluingEPPA.Steiner.ChainValuation.LinkChain

/-!
# Restricted Cayley components in the actual earlier Link family

The old valuation group at mask A has a finite named-generator
presentation, and every smaller-stage Link includes the generators of
M ∩ A. Consequently the M-coloured connected component of a group
block is exactly a left coset of the *actual inclusion range* of
K_(M∩A) in K_A, not of an abstract substitute subgroup.

The relevant intersection and pullback identities for these ranges
are proved independently in LinkProjectors and
LinkRestrictedMatching.
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

/-- Every point of the M-restricted Cayley graph of an earlier K_A has
a component given by the coset of the literal K_(M∩A) inclusion. -/
theorem restricted_block_reach_iff_coset
    (M A : Proper S) (x y : (old A).Carrier) :
    LabelReach (fun e => ((block S old A).matching e).Rel) M.val x y ↔
      y ∈ leftCoset
        (L (Step.meet S M A) A Finset.inter_subset_right).incl.range x := by
  let T : Proper S := Step.meet S M A
  let i : (old T).Carrier →* (old A).Carrier :=
    (L T A Finset.inter_subset_right).incl
  let P : Subgroup (old A).Carrier := i.range
  have hgen : ∀ e, e ∈ M.val → e ∈ (block S old A).active →
      (block S old A).edge e ∈ P := by
    intro e heM heA
    have heT : e ∈ T.val := Finset.mem_inter.mpr ⟨heM, heA⟩
    exact ⟨(old T).edge e, (L T A Finset.inter_subset_right).incl_edge e heT⟩
  have hwordMap : ∀ w : List E, (∀ e ∈ w, e ∈ T.val) →
      (w.map (old A).edge).prod =
        i ((w.map (old T).edge).prod) := by
    intro w
    induction w with
    | nil =>
        intro _
        simp
    | cons e es ih =>
        intro hw
        have he : e ∈ T.val := hw e (by simp)
        have hes : ∀ a ∈ es, a ∈ T.val := by
          intro a ha
          exact hw a (by simp [ha])
        simp only [List.map_cons, List.prod_cons, map_mul]
        rw [ih hes, (L T A Finset.inter_subset_right).incl_edge e he]
  have hwords : ∀ p : (block S old A).Carrier, p ∈ P →
      ∃ w : List E,
        (∀ e ∈ w, e ∈ M.val ∧ e ∈ (block S old A).active) ∧
        (w.map (block S old A).edge).prod = p := by
    intro p hp
    obtain ⟨k, hk⟩ := hp
    obtain ⟨w, hw, hprod⟩ := (old T).generated k
    refine ⟨w, ?_, ?_⟩
    · intro e he
      have heT : e ∈ T.val := hw e he
      exact (Finset.mem_inter.mp heT)
    · have hmap := hwordMap w hw
      rw [hprod] at hmap
      exact hmap.trans hk
  exact cayley_mask_reach_iff_coset
    (block S old A) M.val P hgen hwords x y

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
