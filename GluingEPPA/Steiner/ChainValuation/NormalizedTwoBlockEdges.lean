import GluingEPPA.Steiner.ChainValuation.NormalizedTwoBlockComponent
import GluingEPPA.Steiner.ChainValuation.PushoutChartEdgeEquiv
import GluingEPPA.Steiner.ChainValuation.RestrictedPushoutEdges

/-!
# Genuine M-edge reflection of the normalized two-block component

The exact two-block group normal form gives a bijective map
  K_(M∩A) ⨿_(K_(M∩A∩B)) K_(M∩B)
into the selected connected part of the literal original
K_A ⨿_(K_(A∩B)) K_B pushout.

The original component's labelled edges are the union of genuine
old/new Cayley edges. On each selected coset the smaller-block
chart preserves AND reflects these edges; and a commuting
isomorphism of full attachment diagrams preserves/refects the
quotient union-of-images edge relation. The exact restricted
pushout then reflects edges of the ambient quotient.

This module composes those three checked geometric facts, giving
an explicit M-letter edge-reflecting chart for two adjacent blocks.
It is the local step for the still-open full finite-list chart.
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

/-- For every letter of M, the normalized smaller-mask pushout
chart both preserves and reflects the *actual* labelled edge of
the original two-block quotient. The right side is the selected
union in the original quotient, not an auxiliary edge structure. -/
theorem normalized_twoBlock_genuine_edge_iff
    (M A B : Proper S) (h : (old A).Carrier)
    (k : (old (common S A B)).Carrier)
    (e : E) (he : e ∈ M.val)
    (p q : SetPushout
      (normalizedCommonLeft D S old L M A B)
      (normalizedCommonRight D S old L M A B)
      (normalizedCommonLeft_injective D S old L M A B)
      (normalizedCommonRight_injective D S old L M A B)) :
    let i := left D S old L A B
    let j := right D S old L A B
    let hf := attachLeft_injective h i (left_injective D S old L A B)
    let hj := right_injective D S old L A B
    let F := normalized_twoBlock_equivCovered D S old L M A B h k
    pushoutLabelRel
      (fun e => ((block S old (Step.meet S M A)).matching e).Rel)
      (fun e => ((block S old (Step.meet S M B)).matching e).Rel)
      (normalizedCommonLeft D S old L M A B)
      (normalizedCommonRight D S old L M A B)
      (normalizedCommonLeft_injective D S old L M A B)
      (normalizedCommonRight_injective D S old L M A B)
      e p q ↔
    pushoutLabelRel
      (fun e => ((block S old A).matching e).Rel)
      (fun e => ((block S old B).matching e).Rel)
      (attachLeft h i) j hf hj
      e (F p).val (F q).val := by
  let i := left D S old L A B
  let j := right D S old L A B
  let W := matchedLinkCosetRestriction D S old L M A B h k
  let normL := normalizedCommonLeft D S old L M A B
  let normR := normalizedCommonRight D S old L M A B
  let hnormL := normalizedCommonLeft_injective D S old L M A B
  let hnormR := normalizedCommonRight_injective D S old L M A B
  let hf := attachLeft_injective h i (left_injective D S old L A B)
  let hj := right_injective D S old L A B
  let ca : (old (Step.meet S M A)).Carrier ≃ W.Left :=
    restrictedBlock_cosetEquiv D S old L M A (h * i k)
  let cb : (old (Step.meet S M B)).Carrier ≃ W.Right :=
    restrictedBlock_cosetEquiv D S old L M B (j k)
  let ci : (old (Step.meet S M (common S A B))).Carrier ≃ W.Interface :=
    matchedLinkCoset_interface_equiv D S old L M A B h k
  let F := normalized_twoBlock_equivRestricted D S old L M A B h k
  have hR (x y : (old (Step.meet S M A)).Carrier) :
      ((block S old (Step.meet S M A)).matching e).Rel x y ↔
      ((block S old A).matching e).Rel (ca x).val (ca y).val :=
    restrictedBlock_cosetEquiv_edge_iff D S old L M A
      (h * i k) e he x y
  have hT (x y : (old (Step.meet S M B)).Carrier) :
      ((block S old (Step.meet S M B)).matching e).Rel x y ↔
      ((block S old B).matching e).Rel (cb x).val (cb y).val :=
    restrictedBlock_cosetEquiv_edge_iff D S old L M B
      (j k) e he x y
  have hlocal :
      pushoutLabelRel
        (fun e => ((block S old (Step.meet S M A)).matching e).Rel)
        (fun e => ((block S old (Step.meet S M B)).matching e).Rel)
        normL normR hnormL hnormR e p q ↔
      pushoutLabelRel
        (fun e (x y : W.Left) =>
          ((block S old A).matching e).Rel x.val y.val)
        (fun e (x y : W.Right) =>
          ((block S old B).matching e).Rel x.val y.val)
        W.leftAttach W.rightAttach
        (W.leftAttach_injective hf) (W.rightAttach_injective hj)
        e (F p) (F q) := by
    exact pushoutEquivOfEquivs_edge_iff
      normL normR hnormL hnormR
      W.leftAttach W.rightAttach
      (W.leftAttach_injective hf) (W.rightAttach_injective hj)
      ca cb ci
      (normalized_twoBlock_left_square D S old L M A B h k)
      (normalized_twoBlock_right_square D S old L M A B h k)
      (fun e => ((block S old (Step.meet S M A)).matching e).Rel)
      (fun e => ((block S old (Step.meet S M B)).matching e).Rel)
      (fun e (x y : W.Left) =>
        ((block S old A).matching e).Rel x.val y.val)
      (fun e (x y : W.Right) =>
        ((block S old B).matching e).Rel x.val y.val)
      e hR hT p q
  have hinclusion :
      pushoutLabelRel
        (fun e (x y : W.Left) =>
          ((block S old A).matching e).Rel x.val y.val)
        (fun e (x y : W.Right) =>
          ((block S old B).matching e).Rel x.val y.val)
        W.leftAttach W.rightAttach
        (W.leftAttach_injective hf) (W.rightAttach_injective hj)
        e (F p) (F q) ↔
      pushoutLabelRel
        (fun e => ((block S old A).matching e).Rel)
        (fun e => ((block S old B).matching e).Rel)
        (attachLeft h i) j hf hj
        e (W.intoFull hf hj (F p)) (W.intoFull hf hj (F q)) := by
    change GluingEPPA.Steiner.ChainValuation.MatchedRestriction.quotientEdges
      (fun e (x y : W.Left) =>
        ((block S old A).matching e).Rel x.val y.val)
      (fun e (x y : W.Right) =>
        ((block S old B).matching e).Rel x.val y.val)
      W.leftAttach W.rightAttach
      (W.leftAttach_injective hf) (W.rightAttach_injective hj)
      e (F p) (F q) ↔
      GluingEPPA.Steiner.ChainValuation.MatchedRestriction.quotientEdges
        (fun e => ((block S old A).matching e).Rel)
        (fun e => ((block S old B).matching e).Rel)
        (attachLeft h i) j hf hj
        e (W.intoFull hf hj (F p)) (W.intoFull hf hj (F q))
    exact W.include_edges_iff hf hj
      (fun e => ((block S old A).matching e).Rel)
      (fun e => ((block S old B).matching e).Rel)
      e (F p) (F q)
  change
      pushoutLabelRel
        (fun e => ((block S old (Step.meet S M A)).matching e).Rel)
        (fun e => ((block S old (Step.meet S M B)).matching e).Rel)
        normL normR hnormL hnormR e p q ↔
      pushoutLabelRel
        (fun e => ((block S old A).matching e).Rel)
        (fun e => ((block S old B).matching e).Rel)
        (attachLeft h i) j hf hj
        e (W.intoFull hf hj (F p)) (W.intoFull hf hj (F q))
  exact hlocal.trans hinclusion

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
