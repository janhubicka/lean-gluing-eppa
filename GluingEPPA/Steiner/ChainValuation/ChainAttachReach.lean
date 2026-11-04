import GluingEPPA.Steiner.ChainValuation.PushoutReachBridge
import GluingEPPA.Steiner.ChainValuation.ChainAttach

/-!
# Actual M-components of one separated-chain attachment

The previous bridge concerns the literal SetPushout with a generic union of
labelled edge relations. Here the old relation is `C.matching`, the new one
is the genuine Cayley matching of block `B`, and the quotient relation is
exactly `ChainState.extend.matching`. This identifies real reachability in
one chain-extension step with `GluedReach` of its old/new components.

The geometric component-to-smaller-chain chart is not yet asserted.
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

private abbrev oldRelation (e : E) : C.Space → C.Space → Prop :=
  (C.matching e).Rel

private abbrev newRelation (e : E) : B.Carrier → B.Carrier → Prop :=
  (B.matching e).Rel

/-- The genuine union of the labelled edges in the chain pushout is
definitionally the edge relation of the actual extended chain. -/
theorem chainExtend_edge_iff_pushout
    (e : E) (p q : ExtendedSpace A B C h left right hleft hright) :
    (extendedMatching A B C h left right hleft hright hsep hshared e).Rel p q ↔
    pushoutLabelRel (oldRelation A C) (newRelation B)
      (attachInto C.lastEmbed h left) right
      (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
      hright e p q := by
  constructor
  · intro hh
    change extendedEdgeRel A B C h left right hleft hright e p q at hh
    rcases hh with ⟨x, y, hxy, hx, hy⟩ | ⟨g, he, hx, hy⟩
    · exact Or.inl ⟨x, y, hxy, hx, hy⟩
    · exact Or.inr ⟨g, g * B.edge e, ⟨he, rfl⟩, hx, hy⟩
  · intro hh
    rcases hh with ⟨x, y, hxy, hx, hy⟩ | ⟨g, k, hgk, hx, hy⟩
    · exact Or.inl ⟨x, y, hxy, hx, hy⟩
    · rcases hgk with ⟨he, hk⟩
      subst k
      exact Or.inr ⟨g, he, hx, hy⟩

/-- Literal M-coloured reachability after a chain attachment is equivalent
to old/new M-coloured reachability plus the prescribed attachment. -/
theorem chainExtend_reach_iff_glued
    (M : Finset E) (a b : Sum C.Space B.Carrier) :
    LabelReach
      (fun e => (extendedMatching A B C h left right hleft hright
        hsep hshared e).Rel) M
      (pushoutPoint (attachInto C.lastEmbed h left) right
        (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
        hright a)
      (pushoutPoint (attachInto C.lastEmbed h left) right
        (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
        hright b) ↔
    GluedReach (labelReachSetoid (oldRelation A C) M)
      (labelReachSetoid (newRelation B) M)
      (attachInto C.lastEmbed h left) right a b := by
  have hrel : ∀ (e : E) (p q : ExtendedSpace A B C h left right hleft hright),
      (extendedMatching A B C h left right hleft hright
        hsep hshared e).Rel p q ↔
      pushoutLabelRel (oldRelation A C) (newRelation B)
        (attachInto C.lastEmbed h left) right
        (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
        hright e p q :=
    fun e p q => chainExtend_edge_iff_pushout
      A B C h left right hleft hright hsep hshared e p q
  exact (LabelReach.congr _ _ M hrel _ _).trans
    (pushoutReach_iff_gluedReach
      (oldRelation A C) (newRelation B) M
      (attachInto C.lastEmbed h left) right
      (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
      hright a b)

/-- The preceding theorem stated directly for the matching of
`ChainState.extend`, not for an auxiliary union relation. -/
theorem chainState_extend_reach_iff_glued
    (M : Finset E) (a b : Sum C.Space B.Carrier) :
    LabelReach
      (fun e => ((extend A B C h left right hleft hright
        hsep hshared).matching e).Rel) M
      (pushoutPoint (attachInto C.lastEmbed h left) right
        (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
        hright a)
      (pushoutPoint (attachInto C.lastEmbed h left) right
        (attachInto_injective C.lastEmbed C.lastInjective h left hleft)
        hright b) ↔
    GluedReach (labelReachSetoid (oldRelation A C) M)
      (labelReachSetoid (newRelation B) M)
      (attachInto C.lastEmbed h left) right a b :=
  chainExtend_reach_iff_glued
    A B C h left right hleft hright hsep hshared M a b

end GluingEPPA.Steiner.ChainValuation
