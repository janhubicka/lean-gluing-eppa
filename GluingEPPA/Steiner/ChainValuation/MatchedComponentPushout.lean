import GluingEPPA.Steiner.ChainValuation.RestrictedPushoutExact
import GluingEPPA.Steiner.ChainValuation.CanonicalAttachmentMatching
import GluingEPPA.Steiner.ChainValuation.PushoutReachBridge

/-!
# Exact connected component of a matched pushout

If the M-reachability relations on two labelled graphs have identical
pullbacks to an injectively attached interface, an old component meeting
the interface determines exactly one new component. The union of the
two components in the *literal quotient* is the entire M-component.

In particular, no separate saturation assumption is needed: it follows
from the previously checked matching/no-merging theorem. The result is
stated entirely in terms of genuine labelled edges; no group, coset,
or hypothetical full-stage K_S is used.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w t
variable {E : Type u} {X : Type v} {Y : Type w} {Z : Type t}

/-- The old component through q and the new component through g(k)
have the same attaching preimage whenever q reaches f(k). -/
def matchedComponentRestriction
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hpull : ∀ z z' : Z,
      LabelReach R M (f z) (f z') ↔
      LabelReach T M (g z) (g z'))
    (q : X) (k : Z) (hq : LabelReach R M q (f k)) :
    MatchedRestriction f g where
  left := {x | LabelReach R M q x}
  right := {y | LabelReach T M (g k) y}
  agree := by
    intro z
    constructor
    · intro hz
      exact (hpull k z).mp
        (LabelReach.trans (LabelReach.symm hq) hz)
    · intro hz
      exact LabelReach.trans hq ((hpull k z).mpr hz)

/-- The covered union of the two matched components is the *whole*
component of the old basepoint in the actual injective set-pushout.

This result is stronger than injectivity of a restricted pushout: it
also proves surjectivity onto the full reachable component. -/
theorem matchedComponent_covered_iff_reach
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hpull : ∀ z z' : Z,
      LabelReach R M (f z) (f z') ↔
      LabelReach T M (g z) (g z'))
    (q : X) (k : Z) (hq : LabelReach R M q (f k))
    (hf : Function.Injective f) (hg : Function.Injective g)
    (v : SetPushout f g hf hg) :
    v ∈ (matchedComponentRestriction R T M f g hpull q k hq).Covered hf hg ↔
      LabelReach (pushoutLabelRel R T f g hf hg) M
        (pushoutInl f g hf hg q) v := by
  constructor
  · intro hv
    rcases hv with ⟨x, hx⟩ | ⟨y, hy⟩
    · rw [← hx]
      exact gluedReach_to_pushoutReach R T M f g hf hg
        (GluedReach.old x.property)
    · rw [← hy]
      exact gluedReach_to_pushoutReach R T M f g hf hg
        (GluedReach.trans (GluedReach.old hq)
          (GluedReach.trans (GluedReach.attach k)
            (GluedReach.new y.property)))
  · intro hv
    obtain ⟨a, ha⟩ := pushoutPoint_surjective f g hf hg v
    rw [← ha] at hv
    cases a with
    | inl x =>
        have hglue :
            GluedReach (labelReachSetoid R M) (labelReachSetoid T M)
              f g (.inl q) (.inl x) :=
          (pushoutReach_iff_gluedReach R T M f g hf hg
            (.inl q) (.inl x)).mp hv
        have hr : LabelReach R M q x :=
          gluedReach_old_reflect (labelReachSetoid R M)
            (labelReachSetoid T M) f g hpull hglue
        exact Or.inl ⟨⟨x, hr⟩, ha⟩
    | inr y =>
        have hglue :
            GluedReach (labelReachSetoid R M) (labelReachSetoid T M)
              f g (.inl q) (.inr y) :=
          (pushoutReach_iff_gluedReach R T M f g hf hg
            (.inl q) (.inr y)).mp hv
        have hnew :
            GluedReach (labelReachSetoid R M) (labelReachSetoid T M)
              f g (.inr (g k)) (.inr y) :=
          GluedReach.trans (GluedReach.symm (GluedReach.attach k))
            (GluedReach.trans
              (GluedReach.symm (GluedReach.old hq)) hglue)
        have hr : LabelReach T M (g k) y :=
          gluedReach_new_reflect (labelReachSetoid R M)
            (labelReachSetoid T M) f g hpull hnew
        exact Or.inr ⟨⟨y, hr⟩, ha⟩

/-- Exact equivalence, not just a surjective component cover:
the restricted pushout of an old component and its matched new
component is the literal full component inside the original quotient. -/
noncomputable def matchedComponent_equivReach
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hpull : ∀ z z' : Z,
      LabelReach R M (f z) (f z') ↔
      LabelReach T M (g z) (g z'))
    (q : X) (k : Z) (hq : LabelReach R M q (f k))
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (matchedComponentRestriction R T M f g hpull q k hq).Space hf hg ≃
      {v : SetPushout f g hf hg //
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInl f g hf hg q) v} := by
  let W := matchedComponentRestriction R T M f g hpull q k hq
  let F : W.Space hf hg →
      {v : SetPushout f g hf hg //
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInl f g hf hg q) v} :=
    fun p => ⟨W.intoFull hf hg p,
      (matchedComponent_covered_iff_reach
        R T M f g hpull q k hq hf hg _).mp
        (W.intoFull_mem_covered hf hg p)⟩
  apply Equiv.ofBijective F
  constructor
  · intro a b hab
    apply W.intoFull_injective hf hg
    exact congrArg Subtype.val hab
  · intro v
    have hv : v.val ∈ W.Covered hf hg :=
      (matchedComponent_covered_iff_reach
        R T M f g hpull q k hq hf hg v.val).mpr v.property
    obtain ⟨p, hp⟩ :=
      W.intoFull_surjective_covered hf hg ⟨v.val, hv⟩
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hp

end GluingEPPA.Steiner.ChainValuation
