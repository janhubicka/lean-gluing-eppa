import GluingEPPA.Steiner.ChainValuation.MatchedComponentPushout
import GluingEPPA.Steiner.ChainValuation.ChainComponentPullback

/-!
# Matched components of the actual ChainState extension

The generic component-pushout theorem applies to the exact labelled
matching of ChainState.extend, not just to an auxiliary union of edges.
The required pullback is precisely AttachmentReachCompatible, which is
already supplied by actual LinkChain.step and its last-block invariant.

No global chain-normalization or higher-acyclicity statement is made.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]
variable (A B : GroupBlock E) (C : ChainState E A)
variable (h : A.Carrier)
variable (left : K →* A.Carrier) (right : K →* B.Carrier)
variable (hleft : Function.Injective left) (hright : Function.Injective right)
variable (hsep : Disjoint C.entry (exitSet A h left))
variable (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
  ∃ k : K, left k = A.edge e ∧ right k = B.edge e)

/-- The exact restricted-pushout cover of an attached old component
is precisely the full actual M-component in ChainState.extend. -/
theorem extend_matchedComponent_covered_iff_reach
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (q : C.Space) (k : K)
    (hq : LabelReach (fun e => (C.matching e).Rel) M
      q (attachInto C.lastEmbed h left k))
    (v : ExtendedSpace A B C h left right hleft hright) :
    v ∈ (matchedComponentRestriction
      (fun e => (C.matching e).Rel)
      (fun e => (B.matching e).Rel)
      M (attachInto C.lastEmbed h left) right hpull q k hq).Covered
      (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
      hright ↔
    LabelReach
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel) M
      (oldEmbed A B C h left right hleft hright q) v := by
  exact
    (matchedComponent_covered_iff_reach
      (fun e => (C.matching e).Rel)
      (fun e => (B.matching e).Rel)
      M (attachInto C.lastEmbed h left) right
      hpull q k hq
      (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
      hright v).trans
    ((LabelReach.congr
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel)
      (pushoutLabelRel
        (fun e => (C.matching e).Rel)
        (fun e => (B.matching e).Rel)
        (attachInto C.lastEmbed h left) right
        (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
        hright)
      M
      (fun e x y => chainExtend_edge_iff_pushout
        A B C h left right hleft hright hsep hshared e x y)
      (oldEmbed A B C h left right hleft hright q) v).symm)

end GluingEPPA.Steiner.ChainValuation
