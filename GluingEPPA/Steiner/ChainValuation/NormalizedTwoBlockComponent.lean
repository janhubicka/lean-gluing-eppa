import GluingEPPA.Steiner.ChainValuation.LinkCosetEquiv
import GluingEPPA.Steiner.ChainValuation.MatchedLinkInterfaceEquiv
import GluingEPPA.Steiner.ChainValuation.ActualNormalizedBoundary
import GluingEPPA.Steiner.ChainValuation.PushoutEquiv

/-!
# Exact smaller-mask normalization of a two-block Link component

Let a true earlier Link attachment glue K_A to K_B over K_(A∩B),
with the left attachment translated by h. If a matched M-component
meets the interface at k, its two selected pieces are precisely
the left cosets based at h·i(k) and j(k).

Their own group coordinates are K_(M∩A) and K_(M∩B). The *entire*
matched attaching fibre is coordinatized by K_(M∩A∩B).
The commuting Link squares show that this is an isomorphism of
the whole injective attachment diagram, not merely of its points.

Thus a genuine matched two-block component is the exact pushout of
the corresponding earlier smaller-mask groups. No abelianity,
normality or hypothetical completed K_S is used.

The global finite-chain normalized chart still requires transporting
these coordinates through successive attachments and proving the
full edge-reflection statement.
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

/-- The genuine inclusion of the triple mask into the left
M-restricted block remains injective. -/
theorem normalizedCommonLeft_injective (M A B : Proper S) :
    Function.Injective (normalizedCommonLeft D S old L M A B) := by
  let C : Proper S := Step.meet S M (common S A B)
  let MA : Proper S := Step.meet S M A
  have hsub : C.val ⊆ MA.val := by
    intro e he
    have hm : e ∈ M.val := (Finset.mem_inter.mp he).1
    have hi : e ∈ (common S A B).val := (Finset.mem_inter.mp he).2
    exact Finset.mem_inter.mpr ⟨hm, (Finset.mem_inter.mp hi).1⟩
  change Function.Injective ((L C MA hsub).incl)
  exact Link.injective D (old C) (old MA) hsub (L C MA hsub)

/-- Symmetrically, the genuine triple-mask inclusion is injective
on the right normalized block. -/
theorem normalizedCommonRight_injective (M A B : Proper S) :
    Function.Injective (normalizedCommonRight D S old L M A B) := by
  let C : Proper S := Step.meet S M (common S A B)
  let MB : Proper S := Step.meet S M B
  have hsub : C.val ⊆ MB.val := by
    intro e he
    have hm : e ∈ M.val := (Finset.mem_inter.mp he).1
    have hi : e ∈ (common S A B).val := (Finset.mem_inter.mp he).2
    exact Finset.mem_inter.mpr ⟨hm, (Finset.mem_inter.mp hi).2⟩
  change Function.Injective ((L C MB hsub).incl)
  exact Link.injective D (old C) (old MB) hsub (L C MB hsub)

/-- The two selected translated coset charts and the exact
triple-mask interface chart commute with the *literal* left
attachment of the original blocks. -/
theorem normalized_twoBlock_left_square
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier)
    (t : (old (Step.meet S M (common S A B))).Carrier) :
    let W := matchedLinkCosetRestriction D S old L M A B h k
    let ca := restrictedBlock_cosetEquiv D S old L M A
      (h * left D S old L A B k)
    let ci := matchedLinkCoset_interface_equiv D S old L M A B h k
    ca (normalizedCommonLeft D S old L M A B t) =
      W.leftAttach (ci t) := by
  let i := left D S old L A B
  let p := (L (Step.meet S M A) A Finset.inter_subset_right).incl
  let a := normalizedCommonLeft D S old L M A B
  let c := normalizedCommonInterface D S old L M A B
  have hs : p (a t) = i (c t) :=
    DFunLike.congr_fun (normalizedCommon_left_square D S old L M A B) t
  apply Subtype.ext
  change (h * i k) * p (a t) = h * i (k * c t)
  calc
    (h * i k) * p (a t) = (h * i k) * i (c t) := by rw [hs]
    _ = h * i (k * c t) := by simp only [map_mul, mul_assoc]

/-- The new-block coset chart commutes with the literal
right attachment, in noncommutative word order. -/
theorem normalized_twoBlock_right_square
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier)
    (t : (old (Step.meet S M (common S A B))).Carrier) :
    let W := matchedLinkCosetRestriction D S old L M A B h k
    let cb := restrictedBlock_cosetEquiv D S old L M B
      (right D S old L A B k)
    let ci := matchedLinkCoset_interface_equiv D S old L M A B h k
    cb (normalizedCommonRight D S old L M A B t) =
      W.rightAttach (ci t) := by
  let j := right D S old L A B
  let p := (L (Step.meet S M B) B Finset.inter_subset_right).incl
  let b := normalizedCommonRight D S old L M A B
  let c := normalizedCommonInterface D S old L M A B
  have hs : p (b t) = j (c t) :=
    DFunLike.congr_fun (normalizedCommon_right_square D S old L M A B) t
  apply Subtype.ext
  change (j k) * p (b t) = j (k * c t)
  calc
    (j k) * p (b t) = (j k) * j (c t) := by rw [hs]
    _ = j (k * c t) := by simp only [map_mul, mul_assoc]

/-- The exact full restricted pushout of the two genuine
matched component cosets is equivalent to the pushout of the
actual earlier groups K_(M∩A), K_(M∩B) over K_(M∩A∩B). -/
noncomputable def normalized_twoBlock_equivRestricted
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier) :
    let W := matchedLinkCosetRestriction D S old L M A B h k
    let i := left D S old L A B
    let j := right D S old L A B
    let ha := normalizedCommonLeft_injective D S old L M A B
    let hb := normalizedCommonRight_injective D S old L M A B
    let hf := attachLeft_injective h i (left_injective D S old L A B)
    let hg := right_injective D S old L A B
    SetPushout
      (normalizedCommonLeft D S old L M A B)
      (normalizedCommonRight D S old L M A B)
      ha hb ≃ W.Space hf hg := by
  let i := left D S old L A B
  let j := right D S old L A B
  let W := matchedLinkCosetRestriction D S old L M A B h k
  let ca := restrictedBlock_cosetEquiv D S old L M A (h * i k)
  let cb := restrictedBlock_cosetEquiv D S old L M B (j k)
  let ci := matchedLinkCoset_interface_equiv D S old L M A B h k
  let a := normalizedCommonLeft D S old L M A B
  let b := normalizedCommonRight D S old L M A B
  let ha := normalizedCommonLeft_injective D S old L M A B
  let hb := normalizedCommonRight_injective D S old L M A B
  let hf := attachLeft_injective h i (left_injective D S old L A B)
  let hg := right_injective D S old L A B
  change SetPushout a b ha hb ≃ W.Space hf hg
  exact pushoutEquivOfEquivs a b ha hb
    W.leftAttach W.rightAttach
    (W.leftAttach_injective hf) (W.rightAttach_injective hg)
    ca cb ci
    (normalized_twoBlock_left_square D S old L M A B h k)
    (normalized_twoBlock_right_square D S old L M A B h k)

/-- The normalized smaller-mask two-block chain is therefore
bijective to the **literal selected union** in the original
full two-block quotient, not only to an abstract cover. -/
noncomputable def normalized_twoBlock_equivCovered
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier) :
    let W := matchedLinkCosetRestriction D S old L M A B h k
    let i := left D S old L A B
    let j := right D S old L A B
    let ha := normalizedCommonLeft_injective D S old L M A B
    let hb := normalizedCommonRight_injective D S old L M A B
    let hf := attachLeft_injective h i (left_injective D S old L A B)
    let hg := right_injective D S old L A B
    SetPushout
      (normalizedCommonLeft D S old L M A B)
      (normalizedCommonRight D S old L M A B)
      ha hb ≃
    {q : SetPushout (attachLeft h i) j hf hg // q ∈ W.Covered hf hg} := by
  let W := matchedLinkCosetRestriction D S old L M A B h k
  let i := left D S old L A B
  let j := right D S old L A B
  let hf := attachLeft_injective h i (left_injective D S old L A B)
  let hg := right_injective D S old L A B
  exact (normalized_twoBlock_equivRestricted D S old L M A B h k).trans
    (W.equivCovered hf hg)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
