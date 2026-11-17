import GluingEPPA.Steiner.ChainValuation.PushoutEquiv
import GluingEPPA.Steiner.ChainValuation.LinkStepExactComponent
import GluingEPPA.Steiner.ChainValuation.PushoutChartEdgeEquiv
import GluingEPPA.Steiner.ChainValuation.RestrictedPushoutEdges

/-!
# Exact chart assembly at the literal separated LinkChain.step

This specializes the abstract exact pushout chart theorem to an actual
one-step extension of the recursive valuation's original LinkChain
builder. The selected old component and new restricted Cayley coset,
glued along their entire matching parameter fibre, are already
known to equal the WHOLE reachable component of the extended state.

Thus only the concrete three commuting coordinate equivalences
must still be supplied by the finite-history normalization.
No new assumptions about component saturation or ambient groups.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

open GluingEPPA.Steiner.ChainValuation
attribute [local instance] Classical.propDecidable

universe u v w t
variable {V E : Type u}
variable {X₀ : Type v} {Y₀ : Type w} {Z₀ : Type t}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

/-- An exact chart of the three component pieces induces an actual
equivalence onto the full M-component of one genuine LinkChain.step.

The range uses reachability in the literal completed-matching state,
rather than reachability in an auxiliary point-set pushout. -/
noncomputable def stepComponentChart_equivActual
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hq : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 k)))
    (f₀ : Z₀ → X₀) (g₀ : Z₀ → Y₀)
    (hf₀ : Function.Injective f₀) (hg₀ : Function.Injective g₀)
    (a : X₀ ≃
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).Left)
    (b : Y₀ ≃
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).Right)
    (c : Z₀ ≃
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).Interface)
    (ha : ∀ z : Z₀, a (f₀ z) =
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).leftAttach (c z))
    (hb : ∀ z : Z₀, b (g₀ z) =
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).rightAttach (c z)) :
    SetPushout f₀ g₀ hf₀ hg₀ ≃
      {v : (step D S old L R y hsep).state.Space //
        LabelReach
          (fun e => ((step D S old L R y hsep).state.matching e).Rel)
          M.val
          (oldEmbed (block S old R.current.1) (block S old y.1)
            R.state R.current.2
            (left D S old L R.current.1 y.1)
            (right D S old L R.current.1 y.1)
            (left_injective D S old L R.current.1 y.1)
            (right_injective D S old L R.current.1 y.1) q)
          v} := by
  let W := stepMatchedOldComponentRestriction
    D S old L M R y hprev q k hq
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hf := attachInto_injective
    R.state.lastEmbed R.state.lastInjective R.current.2 i
    (left_injective D S old L R.current.1 y.1)
  let hj := right_injective D S old L R.current.1 y.1
  let F := pushoutEquivOfEquivs f₀ g₀ hf₀ hg₀
    W.leftAttach W.rightAttach
    (W.leftAttach_injective hf) (W.rightAttach_injective hj)
    a b c ha hb
  exact F.trans
    (step_matchedOldComponent_equivFull
      D S old L M R y hsep hprev q k hq)

/-- At the literal separated LinkChain step, the chart assembled from
three smaller coordinate pieces preserves and reflects an actual
labelled matching edge. Neither the selected-union graph nor
a hypothetical ambient group is substituted for the real state. -/
theorem stepComponentChart_genuine_edge_iff
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hq : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 k)))
    (f₀ : Z₀ → X₀) (g₀ : Z₀ → Y₀)
    (hf₀ : Function.Injective f₀) (hg₀ : Function.Injective g₀)
    (a : X₀ ≃
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).Left)
    (b : Y₀ ≃
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).Right)
    (c : Z₀ ≃
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).Interface)
    (ha : ∀ z : Z₀, a (f₀ z) =
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).leftAttach (c z))
    (hb : ∀ z : Z₀, b (g₀ z) =
      (stepMatchedOldComponentRestriction
        D S old L M R y hprev q k hq).rightAttach (c z))
    (R₀ : E → X₀ → X₀ → Prop)
    (T₀ : E → Y₀ → Y₀ → Prop)
    (e : E)
    (hR : ∀ x z : X₀,
      R₀ e x z ↔ (R.state.matching e).Rel (a x).val (a z).val)
    (hT : ∀ x z : Y₀,
      T₀ e x z ↔ ((block S old y.1).matching e).Rel
        (b x).val (b z).val)
    (p r : SetPushout f₀ g₀ hf₀ hg₀) :
    let F := stepComponentChart_equivActual
      D S old L M R y hsep hprev q k hq
      f₀ g₀ hf₀ hg₀ a b c ha hb
    pushoutLabelRel R₀ T₀ f₀ g₀ hf₀ hg₀ e p r ↔
      ((step D S old L R y hsep).state.matching e).Rel
        (F p).val (F r).val := by
  let W := stepMatchedOldComponentRestriction
    D S old L M R y hprev q k hq
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  let hi := left_injective D S old L R.current.1 y.1
  let hj := right_injective D S old L R.current.1 y.1
  let hf := attachInto_injective
    R.state.lastEmbed R.state.lastInjective R.current.2 i hi
  let hdisj := step_attachment_disjoint D S old L R y hsep
  have hshared : ∀ letter,
      letter ∈ A.active → letter ∈ B.active →
      ∃ z, i z = A.edge letter ∧ j z = B.edge letter := by
    intro letter hl hr
    exact shared_edge D S old L R.current.1 y.1 letter hl hr
  let F := pushoutEquivOfEquivs f₀ g₀ hf₀ hg₀
    W.leftAttach W.rightAttach
    (W.leftAttach_injective hf) (W.rightAttach_injective hj)
    a b c ha hb
  have hlocal :
      pushoutLabelRel R₀ T₀ f₀ g₀ hf₀ hg₀ e p r ↔
      pushoutLabelRel
        (fun e (x z : W.Left) => (R.state.matching e).Rel x.val z.val)
        (fun e (x z : W.Right) => (B.matching e).Rel x.val z.val)
        W.leftAttach W.rightAttach
        (W.leftAttach_injective hf) (W.rightAttach_injective hj)
        e (F p) (F r) := by
    exact pushoutEquivOfEquivs_edge_iff
      f₀ g₀ hf₀ hg₀
      W.leftAttach W.rightAttach
      (W.leftAttach_injective hf) (W.rightAttach_injective hj)
      a b c ha hb R₀ T₀
      (fun e (x z : W.Left) => (R.state.matching e).Rel x.val z.val)
      (fun e (x z : W.Right) => (B.matching e).Rel x.val z.val)
      e hR hT p r
  have hfull :
      pushoutLabelRel
        (fun e (x z : W.Left) => (R.state.matching e).Rel x.val z.val)
        (fun e (x z : W.Right) => (B.matching e).Rel x.val z.val)
        W.leftAttach W.rightAttach
        (W.leftAttach_injective hf) (W.rightAttach_injective hj)
        e (F p) (F r) ↔
      pushoutLabelRel
        (fun e => (R.state.matching e).Rel)
        (fun e => (B.matching e).Rel)
        (attachInto R.state.lastEmbed R.current.2 i) j hf hj
        e (W.intoFull hf hj (F p))
          (W.intoFull hf hj (F r)) := by
    exact W.include_edges_iff hf hj
      (fun e => (R.state.matching e).Rel)
      (fun e => (B.matching e).Rel) e (F p) (F r)
  have hActual :
      pushoutLabelRel
        (fun e => (R.state.matching e).Rel)
        (fun e => (B.matching e).Rel)
        (attachInto R.state.lastEmbed R.current.2 i) j hf hj
        e (W.intoFull hf hj (F p))
          (W.intoFull hf hj (F r)) ↔
      ((step D S old L R y hsep).state.matching e).Rel
        (W.intoFull hf hj (F p))
          (W.intoFull hf hj (F r)) := by
    exact (chainExtend_edge_iff_pushout
      A B R.state R.current.2 i j hi hj hdisj hshared
      e (W.intoFull hf hj (F p)) (W.intoFull hf hj (F r))).symm
  change pushoutLabelRel R₀ T₀ f₀ g₀ hf₀ hg₀ e p r ↔
    ((step D S old L R y hsep).state.matching e).Rel
      (W.intoFull hf hj (F p)) (W.intoFull hf hj (F r))
  exact (hlocal.trans hfull).trans hActual

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
