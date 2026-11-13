import GluingEPPA.Steiner.ChainValuation.OldComponentLinkFibre
import GluingEPPA.Steiner.ChainValuation.RestrictedPushoutExact

/-!
# Exact component-piece pushout at an actual LinkChain extension

The old selected piece is a whole M-component of the *previous
chain*, while the new selected piece is a coset in the newly
attached Cayley group K_B. The last-block invariant proves that
their complete attaching parameter preimages coincide.

Thus the exact restricted pushout is bijective to the literal
union of these two pieces inside the full actual chain attachment.
This is the geometric extension step for building a normalized
component model; it is not yet a full all-length chain theorem.
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

/-- An old M-component and the corresponding coset in the new
Cayley block satisfy the exact matched-preimage condition.
The old component is selected by an arbitrary old-chain vertex q
and a single attaching parameter k which that component meets. -/
def stepMatchedOldComponentRestriction
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hq : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 k))) :
    MatchedRestriction
      (attachInto R.state.lastEmbed R.current.2
        (left D S old L R.current.1 y.1))
      (right D S old L R.current.1 y.1) where
  left := {x | LabelReach
    (fun e => (R.state.matching e).Rel) M.val q x}
  right := leftCoset
    (restrictedSubgroup D S old L M y.1)
    (right D S old L R.current.1 y.1 k)
  agree := by
    intro z
    exact step_oldComponent_attachment_fibre_iff D S old L
      M R y hprev q k hq z

/-- The literal exact pushout of the old *entire* component and
the new coset is bijective to their true selected union in the
extended chain quotient. No surrogate ambient group or assumed
matching of attachment parameters is used. -/
noncomputable def stepMatchedOldComponent_equivCovered
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hq : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 k))) :
    let W := stepMatchedOldComponentRestriction D S old L
      M R y hprev q k hq
    let i := left D S old L R.current.1 y.1
    let j := right D S old L R.current.1 y.1
    let hf := attachInto_injective
      R.state.lastEmbed R.state.lastInjective R.current.2 i
      (left_injective D S old L R.current.1 y.1)
    let hj := right_injective D S old L R.current.1 y.1
    W.Space hf hj ≃
      {v : SetPushout
        (attachInto R.state.lastEmbed R.current.2 i) j hf hj //
        v ∈ W.Covered hf hj} :=
  (stepMatchedOldComponentRestriction D S old L M R y
    hprev q k hq).equivCovered
      (attachInto_injective
        R.state.lastEmbed R.state.lastInjective R.current.2
        (left D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1))
      (right_injective D S old L R.current.1 y.1)

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
