import GluingEPPA.Steiner.ChainValuation.CanonicalAttachmentMatching
import GluingEPPA.Steiner.ChainValuation.ChainAttachReach

/-!
# No-merging of actual M-components under a chain attachment

The old and new *actual* M-path relations must agree after restriction to
the common attaching space. Under precisely that hypothesis, the previous
component-matching theorem applies to the genuine `ChainState.extend`
quotient, without replacing it by an auxiliary object.

A later induction must establish this pullback agreement from the earlier
Link projector intersection identities and from the interval/coset invariant.
It is deliberately an explicit hypothesis here.
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

/-- The exact condition comparing M-components at the points of the
attaching subgroup. Its proof for actual recursive Links is the
outstanding geometric restriction obligation. -/
def AttachmentReachCompatible (M : Finset E) : Prop :=
  ∀ k l : K,
    LabelReach (fun e => (C.matching e).Rel) M
      (attachInto C.lastEmbed h left k)
      (attachInto C.lastEmbed h left l) ↔
    LabelReach (fun e => (B.matching e).Rel) M (right k) (right l)

/-- A real M-component in one extended chain is a class of the canonical
matching of the old and new M-components, provided their attachment
pullbacks agree. -/
theorem chainExtend_reach_iff_component_matching
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (a b : Sum C.Space B.Carrier) :
    LabelReach
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel) M
      (pushoutPoint (attachInto C.lastEmbed h left) right
        (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
        hright a)
      (pushoutPoint (attachInto C.lastEmbed h left) right
        (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
        hright b) ↔
    componentClass
        (labelReachSetoid (fun e => (C.matching e).Rel) M)
        (labelReachSetoid (fun e => (B.matching e).Rel) M)
        (canonicalAttachmentMatching
          (labelReachSetoid (fun e => (C.matching e).Rel) M)
          (labelReachSetoid (fun e => (B.matching e).Rel) M)
          (attachInto C.lastEmbed h left) right hpull) a =
    componentClass
        (labelReachSetoid (fun e => (C.matching e).Rel) M)
        (labelReachSetoid (fun e => (B.matching e).Rel) M)
        (canonicalAttachmentMatching
          (labelReachSetoid (fun e => (C.matching e).Rel) M)
          (labelReachSetoid (fun e => (B.matching e).Rel) M)
          (attachInto C.lastEmbed h left) right hpull) b := by
  exact (chainState_extend_reach_iff_glued
    A B C h left right hleft hright hsep hshared M a b).trans
    (gluedReach_iff_canonical_matching
      (labelReachSetoid (fun e => (C.matching e).Rel) M)
      (labelReachSetoid (fun e => (B.matching e).Rel) M)
      (attachInto C.lastEmbed h left) right hpull a b)

/-- Two original chain components cannot merge as a result of attaching
a new block. This uses the actual completed matching of the extended state,
not an abstract graph without fixed-point actions. -/
theorem chainExtend_old_components_reflect
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (x y : C.Space)
    (hxy : LabelReach
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel) M
      (oldEmbed A B C h left right hleft hright x)
      (oldEmbed A B C h left right hleft hright y)) :
    LabelReach (fun e => (C.matching e).Rel) M x y := by
  have hg : GluedReach
      (labelReachSetoid (fun e => (C.matching e).Rel) M)
      (labelReachSetoid (fun e => (B.matching e).Rel) M)
      (attachInto C.lastEmbed h left) right (.inl x) (.inl y) :=
    (chainState_extend_reach_iff_glued
      A B C h left right hleft hright hsep hshared M
        (.inl x) (.inl y)).mp hxy
  exact gluedReach_old_reflect
    (labelReachSetoid (fun e => (C.matching e).Rel) M)
    (labelReachSetoid (fun e => (B.matching e).Rel) M)
    (attachInto C.lastEmbed h left) right hpull hg

/-- Nor can an attachment identify two different new-block M-components. -/
theorem chainExtend_new_components_reflect
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (x y : B.Carrier)
    (hxy : LabelReach
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel) M
      (newEmbed A B C h left right hleft hright x)
      (newEmbed A B C h left right hleft hright y)) :
    LabelReach (fun e => (B.matching e).Rel) M x y := by
  have hg : GluedReach
      (labelReachSetoid (fun e => (C.matching e).Rel) M)
      (labelReachSetoid (fun e => (B.matching e).Rel) M)
      (attachInto C.lastEmbed h left) right (.inr x) (.inr y) :=
    (chainState_extend_reach_iff_glued
      A B C h left right hleft hright hsep hshared M
        (.inr x) (.inr y)).mp hxy
  exact gluedReach_new_reflect
    (labelReachSetoid (fun e => (C.matching e).Rel) M)
    (labelReachSetoid (fun e => (B.matching e).Rel) M)
    (attachInto C.lastEmbed h left) right hpull hg

end GluingEPPA.Steiner.ChainValuation
