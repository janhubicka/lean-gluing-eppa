import GluingEPPA.Steiner.ChainValuation.PushoutEquiv
import GluingEPPA.Steiner.ChainValuation.MatchedComponentPushout

/-!
# Composing exact component charts through one matched attachment

The normalized component construction has two logically distinct
inputs: (1) the selected old and new pieces, with a complete common
attaching interface, and (2) coordinate charts for those pieces
and that interface. Previously checked exact pushout and no-merging
theorems are sufficient to combine them.

This module proves the general induction *assembly* lemma:
if a matched restriction W of an injective labelled attachment
covers precisely one genuine M-component, and the two selected
pieces and the WHOLE interface have commuting bijective charts
from smaller structures X₀,Y₀,Z₀, then the smaller exact pushout
is bijective to the entire actual M-component in the full quotient.

The second theorem specializes the coverage premise to the
checked canonical matching/no-merging lemma. There is no
surjectivity-only cover, fictional full-stage K_S, or additional
component-saturation assumption.

The concrete finite-history normalization still needs to supply
the old smaller-chain chart, the new restricted Cayley coset chart,
and the normalized triple-mask interface charts at every step.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w t v' w' t'
variable {E : Type u} {X : Type v} {Y : Type w} {Z : Type t}
variable {X₀ : Type v'} {Y₀ : Type w'} {Z₀ : Type t'}
variable {f : Z → X} {g : Z → Y}

namespace MatchedRestriction

/-- The exact pushout of any commuting bijective charts on the
selected old component, selected new component, and **entire**
attaching interface is equivalent to a full reachable component
of the original literal pushout.

The only geometric premise is explicitly that the chosen matched
restriction covers that full component, rather than just a subset.
The checked canonical matching construction supplies this premise. -/
noncomputable def equivFullReachOfCharts
    (W : MatchedRestriction f g)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (q : X)
    (hcover : ∀ v : SetPushout f g hf hg,
      v ∈ W.Covered hf hg ↔
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInl f g hf hg q) v)
    (f₀ : Z₀ → X₀) (g₀ : Z₀ → Y₀)
    (hf₀ : Function.Injective f₀) (hg₀ : Function.Injective g₀)
    (a : X₀ ≃ W.Left) (b : Y₀ ≃ W.Right)
    (c : Z₀ ≃ W.Interface)
    (ha : ∀ z : Z₀, a (f₀ z) = W.leftAttach (c z))
    (hb : ∀ z : Z₀, b (g₀ z) = W.rightAttach (c z)) :
    SetPushout f₀ g₀ hf₀ hg₀ ≃
      {v : SetPushout f g hf hg //
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInl f g hf hg q) v} := by
  let F := pushoutEquivOfEquivs
    f₀ g₀ hf₀ hg₀ W.leftAttach W.rightAttach
    (W.leftAttach_injective hf) (W.rightAttach_injective hg)
    a b c ha hb
  let G : {v : SetPushout f g hf hg // v ∈ W.Covered hf hg} →
      {v : SetPushout f g hf hg //
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInl f g hf hg q) v} :=
    fun v => ⟨v.val, (hcover v.val).mp v.property⟩
  have hInj : Function.Injective G := by
    intro v w hvw
    exact Subtype.ext (congrArg Subtype.val hvw)
  have hSurj : Function.Surjective G := by
    intro v
    refine ⟨⟨v.val, (hcover v.val).mpr v.property⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact F.trans ((W.equivCovered hf hg).trans
    (Equiv.ofBijective G ⟨hInj, hSurj⟩))

end MatchedRestriction

/-- In the canonical matched old/new M-component of an actual
injective pushout, the full-component coverage condition required
above follows from earlier checked component-class matching.

Consequently, **only the three commuting coordinate equivalences**
need to be constructed at a given normalization step. -/
noncomputable def matchedComponent_equivFullReachOfCharts
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hpull : ∀ z z' : Z,
      LabelReach R M (f z) (f z') ↔
      LabelReach T M (g z) (g z'))
    (q : X) (k : Z) (hq : LabelReach R M q (f k))
    (f₀ : Z₀ → X₀) (g₀ : Z₀ → Y₀)
    (hf₀ : Function.Injective f₀) (hg₀ : Function.Injective g₀)
    (a : X₀ ≃
      (matchedComponentRestriction R T M f g hpull q k hq).Left)
    (b : Y₀ ≃
      (matchedComponentRestriction R T M f g hpull q k hq).Right)
    (c : Z₀ ≃
      (matchedComponentRestriction R T M f g hpull q k hq).Interface)
    (ha : ∀ z : Z₀, a (f₀ z) =
      (matchedComponentRestriction R T M f g hpull q k hq).leftAttach
        (c z))
    (hb : ∀ z : Z₀, b (g₀ z) =
      (matchedComponentRestriction R T M f g hpull q k hq).rightAttach
        (c z)) :
    SetPushout f₀ g₀ hf₀ hg₀ ≃
      {v : SetPushout f g hf hg //
        LabelReach (pushoutLabelRel R T f g hf hg) M
          (pushoutInl f g hf hg q) v} := by
  let W := matchedComponentRestriction R T M f g hpull q k hq
  exact W.equivFullReachOfCharts hf hg R T M q
    (fun v => matchedComponent_covered_iff_reach
      R T M f g hpull q k hq hf hg v)
    f₀ g₀ hf₀ hg₀ a b c ha hb

end GluingEPPA.Steiner.ChainValuation
