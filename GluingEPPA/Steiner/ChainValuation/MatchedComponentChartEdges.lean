import GluingEPPA.Steiner.ChainValuation.MatchedComponentChartExtension
import GluingEPPA.Steiner.ChainValuation.PushoutChartEdgeEquiv
import GluingEPPA.Steiner.ChainValuation.RestrictedPushoutEdges

/-!
# Genuine-edge reflection for a full matched-component chart

The exact matched-component pushout theorem supplies a bijection from
the normalized smaller attachment onto the whole actual M-reachable
component. The point-set equivalence alone is not sufficient for
the recursive valuation: the chart must also reflect every genuine
letter edge, including those witnessed on the opposite side of the
attaching interface.

This lemma combines two verified local facts:

* a commuting equivalence of *all three* pieces of a diagram
  preserves and reflects the union-of-images edge relation;
* the exact selected quotient induces exactly the original edges,
  rather than merely preserving them.

The result is a full component edge-reflecting chart, conditional
only on the concrete three coordinate equivalences and their
edge-reflection properties. The finite-history chain induction must
still construct these concrete charts at each attachment.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w t v' w' t'
variable {E : Type u} {X : Type v} {Y : Type w} {Z : Type t}
variable {X₀ : Type v'} {Y₀ : Type w'} {Z₀ : Type t'}
variable {f : Z → X} {g : Z → Y}

namespace MatchedRestriction

/-- The full-component chart assembled from three commuting
equivalences preserves **and reflects** actual quotient edges.

Unlike a point-set equivalence, this statement proves the exact
condition needed for conjugating the completed letter permutations.
The right-hand side uses the genuine edge relation of the original
full quotient, not an artificial restricted matching. -/
theorem equivFullReachOfCharts_edge_iff
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
    (hb : ∀ z : Z₀, b (g₀ z) = W.rightAttach (c z))
    (R₀ : E → X₀ → X₀ → Prop) (T₀ : E → Y₀ → Y₀ → Prop)
    (e : E)
    (hR : ∀ x y, R₀ e x y ↔ R e (a x).val (a y).val)
    (hT : ∀ x y, T₀ e x y ↔ T e (b x).val (b y).val)
    (p r : SetPushout f₀ g₀ hf₀ hg₀) :
    pushoutLabelRel R₀ T₀ f₀ g₀ hf₀ hg₀ e p r ↔
      pushoutLabelRel R T f g hf hg e
        ((W.equivFullReachOfCharts hf hg R T M q hcover
          f₀ g₀ hf₀ hg₀ a b c ha hb) p).val
        ((W.equivFullReachOfCharts hf hg R T M q hcover
          f₀ g₀ hf₀ hg₀ a b c ha hb) r).val := by
  let F := pushoutEquivOfEquivs
    f₀ g₀ hf₀ hg₀ W.leftAttach W.rightAttach
    (W.leftAttach_injective hf) (W.rightAttach_injective hg)
    a b c ha hb
  have hlocal :
      pushoutLabelRel R₀ T₀ f₀ g₀ hf₀ hg₀ e p r ↔
      pushoutLabelRel
        (fun e (x y : W.Left) => R e x.val y.val)
        (fun e (x y : W.Right) => T e x.val y.val)
        W.leftAttach W.rightAttach
        (W.leftAttach_injective hf) (W.rightAttach_injective hg)
        e (F p) (F r) := by
    exact pushoutEquivOfEquivs_edge_iff
      f₀ g₀ hf₀ hg₀
      W.leftAttach W.rightAttach
      (W.leftAttach_injective hf) (W.rightAttach_injective hg)
      a b c ha hb
      R₀ T₀
      (fun e (x y : W.Left) => R e x.val y.val)
      (fun e (x y : W.Right) => T e x.val y.val)
      e hR hT p r
  have hfull :
      pushoutLabelRel
        (fun e (x y : W.Left) => R e x.val y.val)
        (fun e (x y : W.Right) => T e x.val y.val)
        W.leftAttach W.rightAttach
        (W.leftAttach_injective hf) (W.rightAttach_injective hg)
        e (F p) (F r) ↔
      pushoutLabelRel R T f g hf hg e
        (W.intoFull hf hg (F p)) (W.intoFull hf hg (F r)) := by
    exact W.include_edges_iff hf hg R T e (F p) (F r)
  change pushoutLabelRel R₀ T₀ f₀ g₀ hf₀ hg₀ e p r ↔
    pushoutLabelRel R T f g hf hg e
      (W.intoFull hf hg (F p)) (W.intoFull hf hg (F r))
  exact hlocal.trans hfull

end MatchedRestriction

end GluingEPPA.Steiner.ChainValuation
