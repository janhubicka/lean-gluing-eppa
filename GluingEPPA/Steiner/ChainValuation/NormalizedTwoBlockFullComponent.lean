import GluingEPPA.Steiner.ChainValuation.NormalizedTwoBlockEdges
import GluingEPPA.Steiner.ChainValuation.MatchedComponentPushout

/-!
# The normalized two-block chart is the entire actual M-component

The exact normalized smaller-mask two-block chart was previously
proved bijective to the selected union of two matched restricted
cosets, and it preserves and reflects every genuine M-labelled
edge. Here we close the remaining *component-surjectivity* step.

The earlier Link subgroup pullback identity proves that actual
M-reachability has identical pullbacks to the common K_(A∩B).
The checked matching-gluing theorem then identifies the selected
union with the entire M-component of the chosen attaching point.

Composing with the checked two-block chart gives a bijection
onto the complete genuine connected component. This is still a
two-block theorem, not the arbitrary finite-list normalization.
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

/-- Exact agreement of the M-reachability relations on the two
actual earlier Cayley groups when restricted to their common Link
interface. The old attachment is translated by h, with no
normality/abelianity assumption. -/
theorem twoBlock_attachmentReachCompatible
    (M A B : Proper S) (h : (old A).Carrier)
    (z z' : (old (common S A B)).Carrier) :
    LabelReach
      (fun e => ((block S old A).matching e).Rel) M.val
      (h * left D S old L A B z)
      (h * left D S old L A B z') ↔
    LabelReach
      (fun e => ((block S old B).matching e).Rel) M.val
      (right D S old L A B z)
      (right D S old L A B z') := by
  let i := left D S old L A B
  let j := right D S old L A B
  have hl := restricted_block_reach_iff_coset D S old L
    M A (h * i z) (h * i z')
  have hr := restricted_block_reach_iff_coset D S old L
    M B (j z) (j z')
  exact hl.trans ((restrictedLink_fibre_mem_iff
    D S old L M A B h z z').trans hr.symm)

/-- The exact union selected by matchedLinkCosetRestriction is
precisely the *whole* M-component of the actual old attaching
vertex inside the literal injective two-block pushout. -/
theorem matchedLinkCoset_covered_iff_full_component
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier)
    (v : SetPushout
      (attachLeft h (left D S old L A B))
      (right D S old L A B)
      (attachLeft_injective h (left D S old L A B)
        (left_injective D S old L A B))
      (right_injective D S old L A B)) :
    let i := left D S old L A B
    let j := right D S old L A B
    let hf := attachLeft_injective h i (left_injective D S old L A B)
    let hj := right_injective D S old L A B
    let W := matchedLinkCosetRestriction D S old L M A B h k
    v ∈ W.Covered hf hj ↔
      LabelReach
        (pushoutLabelRel
          (fun e => ((block S old A).matching e).Rel)
          (fun e => ((block S old B).matching e).Rel)
          (attachLeft h i) j hf hj)
        M.val
        (pushoutInl (attachLeft h i) j hf hj (h * i k))
        v := by
  let i := left D S old L A B
  let j := right D S old L A B
  let hf := attachLeft_injective h i (left_injective D S old L A B)
  let hj := right_injective D S old L A B
  let W := matchedLinkCosetRestriction D S old L M A B h k
  let hpull : ∀ z z' : (old (common S A B)).Carrier,
      LabelReach (fun e => ((block S old A).matching e).Rel)
        M.val (h * i z) (h * i z') ↔
      LabelReach (fun e => ((block S old B).matching e).Rel)
        M.val (j z) (j z') :=
    twoBlock_attachmentReachCompatible D S old L M A B h
  let U := matchedComponentRestriction
    (fun e => ((block S old A).matching e).Rel)
    (fun e => ((block S old B).matching e).Rel)
    M.val (attachLeft h i) j hpull
    (h * i k) k (LabelReach.refl _)
  have hcovered : W.Covered hf hj = U.Covered hf hj := by
    ext q
    change
      ((∃ x : W.Left,
        pushoutInl (attachLeft h i) j hf hj x.val = q) ∨
       (∃ y : W.Right,
        pushoutInr (attachLeft h i) j hf hj y.val = q)) ↔
      ((∃ x : U.Left,
        pushoutInl (attachLeft h i) j hf hj x.val = q) ∨
       (∃ y : U.Right,
        pushoutInr (attachLeft h i) j hf hj y.val = q))
    constructor
    · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
      · exact Or.inl ⟨⟨x.val,
          (restricted_block_reach_iff_coset D S old L
            M A (h * i k) x.val).mpr x.property⟩, hx⟩
      · exact Or.inr ⟨⟨y.val,
          (restricted_block_reach_iff_coset D S old L
            M B (j k) y.val).mpr y.property⟩, hy⟩
    · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
      · exact Or.inl ⟨⟨x.val,
          (restricted_block_reach_iff_coset D S old L
            M A (h * i k) x.val).mp x.property⟩, hx⟩
      · exact Or.inr ⟨⟨y.val,
          (restricted_block_reach_iff_coset D S old L
            M B (j k) y.val).mp y.property⟩, hy⟩
  rw [hcovered]
  exact matchedComponent_covered_iff_reach
    (fun e => ((block S old A).matching e).Rel)
    (fun e => ((block S old B).matching e).Rel)
    M.val (attachLeft h i) j hpull
    (h * i k) k (LabelReach.refl _) hf hj v

/-- The genuine two-block smaller-mask pushout is equivalent
to the *entire* M-component of its image in the actual original
two-block quotient. No selected points remain unaccounted for. -/
noncomputable def normalized_twoBlock_equivFullComponent
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier) :
    let i := left D S old L A B
    let j := right D S old L A B
    let ha := normalizedCommonLeft_injective D S old L M A B
    let hb := normalizedCommonRight_injective D S old L M A B
    let hf := attachLeft_injective h i (left_injective D S old L A B)
    let hj := right_injective D S old L A B
    SetPushout
      (normalizedCommonLeft D S old L M A B)
      (normalizedCommonRight D S old L M A B)
      ha hb ≃
    {v : SetPushout (attachLeft h i) j hf hj //
      LabelReach
        (pushoutLabelRel
          (fun e => ((block S old A).matching e).Rel)
          (fun e => ((block S old B).matching e).Rel)
          (attachLeft h i) j hf hj)
        M.val
        (pushoutInl (attachLeft h i) j hf hj (h * i k)) v} := by
  let i := left D S old L A B
  let j := right D S old L A B
  let hf := attachLeft_injective h i (left_injective D S old L A B)
  let hj := right_injective D S old L A B
  let W := matchedLinkCosetRestriction D S old L M A B h k
  let F := normalized_twoBlock_equivCovered D S old L M A B h k
  let G :
      {v : SetPushout (attachLeft h i) j hf hj // v ∈ W.Covered hf hj} ≃
      {v : SetPushout (attachLeft h i) j hf hj //
        LabelReach
          (pushoutLabelRel
            (fun e => ((block S old A).matching e).Rel)
            (fun e => ((block S old B).matching e).Rel)
            (attachLeft h i) j hf hj)
          M.val
          (pushoutInl (attachLeft h i) j hf hj (h * i k)) v} :=
    { toFun := fun z => ⟨z.val,
      (matchedLinkCoset_covered_iff_full_component
        D S old L M A B h k z.val).mp z.property⟩
    invFun := fun z => ⟨z.val,
      (matchedLinkCoset_covered_iff_full_component
        D S old L M A B h k z.val).mpr z.property⟩
    left_inv := by
      intro z
      apply Subtype.ext
      rfl
    right_inv := by
      intro z
      apply Subtype.ext
      rfl }
  exact F.trans G

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
