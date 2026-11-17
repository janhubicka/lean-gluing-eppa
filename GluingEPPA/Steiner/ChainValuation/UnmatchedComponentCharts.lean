import GluingEPPA.Steiner.ChainValuation.UnmatchedComponentPushout

/-!
# Exact labelled charts for components missing the attaching interface

A component of one side which never reaches an attaching parameter is
*literally the entire component* in the original injective pushout.
The earlier unmatched-component lemmas identified its image; we upgrade
that result to an equivalence and to two-way reflection of every
genuine labelled edge.

This addresses the previously separate unmatched-root cases of the
Part II finite-chain normalization induction. Neither old/new
component matching nor pullback compatibility is assumed here.

An e-edge from the *other* side would force one of the two component
vertices to belong to the attaching interface, contradicting the
unmatched hypothesis. Thus the reflection statement holds for every
letter, even outside the mask M.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w t
variable {E : Type u} {X : Type v} {Y : Type w} {Z : Type t}

/-- Exact equivalence from a whole unattached NEW M-component to
its genuine counterpart in the full labelled quotient. -/
noncomputable def unmatchedNewComponentEquiv
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (q : Y) (hnomeet : ∀ z : Z, ¬ LabelReach T M q (g z)) :
    {y : Y // LabelReach T M q y} ≃
      {v : SetPushout f g hf hg //
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInr f g hf hg q) v} := by
  let F : {y : Y // LabelReach T M q y} →
      {v : SetPushout f g hf hg //
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInr f g hf hg q) v} :=
    fun y => ⟨pushoutInr f g hf hg y.val,
      (unmatchedNewComponent_iff_reach R T M f g hf hg q
        hnomeet (pushoutInr f g hf hg y.val)).mpr
        ⟨y.val, y.property, rfl⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro a b hab
    apply Subtype.ext
    exact (pushoutInr_injective f g hf hg)
      (congrArg Subtype.val hab)
  · intro v
    obtain ⟨y, hy, hv⟩ :=
      (unmatchedNewComponent_iff_reach
        R T M f g hf hg q hnomeet v.val).mp v.property
    refine ⟨⟨y, hy⟩, ?_⟩
    exact Subtype.ext hv

/-- Both directions of genuine labelled-edge preservation hold
for the exact unattached new-component chart. An old-side edge
between two points of this component would contradict hnomeet. -/
theorem unmatchedNewComponentEquiv_edge_iff
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (q : Y) (hnomeet : ∀ z : Z, ¬ LabelReach T M q (g z))
    (e : E)
    (a b : {y : Y // LabelReach T M q y}) :
    T e a.val b.val ↔
      pushoutLabelRel R T f g hf hg e
        ((unmatchedNewComponentEquiv R T M f g hf hg q
          hnomeet) a).val
        ((unmatchedNewComponentEquiv R T M f g hf hg q
          hnomeet) b).val := by
  change T e a.val b.val ↔
    pushoutLabelRel R T f g hf hg e
      (pushoutInr f g hf hg a.val) (pushoutInr f g hf hg b.val)
  constructor
  · intro hab
    exact Or.inr ⟨a.val, b.val, hab, rfl, rfl⟩
  · intro h
    rcases h with ⟨x, y, hxy, hx, hy⟩ | ⟨x, y, hxy, hx, hy⟩
    · obtain ⟨k, _, hk⟩ :=
        (pushoutInl_eq_inr_iff f g hf hg x a.val).mp hx
      have hreach : LabelReach T M q (g k) := by
        rw [hk]
        exact a.property
      exact False.elim (hnomeet k hreach)
    · have ha : x = a.val :=
        (pushoutInr_injective f g hf hg) hx
      have hb : y = b.val :=
        (pushoutInr_injective f g hf hg) hy
      simpa only [ha, hb] using hxy

/-- Exact equivalence from a whole unattached OLD M-component to
its genuine component in the complete quotient. -/
noncomputable def unmatchedOldComponentEquiv
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (q : X) (hnomeet : ∀ z : Z, ¬ LabelReach R M q (f z)) :
    {x : X // LabelReach R M q x} ≃
      {v : SetPushout f g hf hg //
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInl f g hf hg q) v} := by
  let F : {x : X // LabelReach R M q x} →
      {v : SetPushout f g hf hg //
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInl f g hf hg q) v} :=
    fun x => ⟨pushoutInl f g hf hg x.val,
      (unmatchedOldComponent_iff_reach R T M f g hf hg q
        hnomeet (pushoutInl f g hf hg x.val)).mpr
        ⟨x.val, x.property, rfl⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro a b hab
    apply Subtype.ext
    exact (pushoutInl_injective f g hf hg)
      (congrArg Subtype.val hab)
  · intro v
    obtain ⟨x, hx, hv⟩ :=
      (unmatchedOldComponent_iff_reach
        R T M f g hf hg q hnomeet v.val).mp v.property
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hv

/-- Symmetric edge reflection for an old M-component which does
not meet the attaching interface. -/
theorem unmatchedOldComponentEquiv_edge_iff
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (q : X) (hnomeet : ∀ z : Z, ¬ LabelReach R M q (f z))
    (e : E)
    (a b : {x : X // LabelReach R M q x}) :
    R e a.val b.val ↔
      pushoutLabelRel R T f g hf hg e
        ((unmatchedOldComponentEquiv R T M f g hf hg q
          hnomeet) a).val
        ((unmatchedOldComponentEquiv R T M f g hf hg q
          hnomeet) b).val := by
  change R e a.val b.val ↔
    pushoutLabelRel R T f g hf hg e
      (pushoutInl f g hf hg a.val) (pushoutInl f g hf hg b.val)
  constructor
  · intro hab
    exact Or.inl ⟨a.val, b.val, hab, rfl, rfl⟩
  · intro h
    rcases h with ⟨x, y, hxy, hx, hy⟩ | ⟨x, y, hxy, hx, hy⟩
    · have ha : x = a.val :=
        (pushoutInl_injective f g hf hg) hx
      have hb : y = b.val :=
        (pushoutInl_injective f g hf hg) hy
      simpa only [ha, hb] using hxy
    · obtain ⟨k, hk, _⟩ :=
        (pushoutInl_eq_inr_iff f g hf hg a.val x).mp hx.symm
      have hreach : LabelReach R M q (f k) := by
        rw [hk]
        exact a.property
      exact False.elim (hnomeet k hreach)

end GluingEPPA.Steiner.ChainValuation
