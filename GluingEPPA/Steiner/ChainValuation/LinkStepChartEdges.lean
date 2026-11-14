import GluingEPPA.Steiner.ChainValuation.PushoutEquiv
import GluingEPPA.Steiner.ChainValuation.LinkStepExactComponent

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

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
