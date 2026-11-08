import GluingEPPA.Steiner.ChainValuation.ActualNormalizedBoundary
import GluingEPPA.Steiner.ChainValuation.LinkStepCoset
import GluingEPPA.Steiner.ChainValuation.Pushout

/-!
# Normalized boundary shifts for an arbitrary old LinkChain component

At the actual next LinkChain attachment, the old M-component is a
component of the *whole previously constructed chain*. Its nonempty
intersection with the preceding last Cayley block is one translated
coset g·K_(M∩A).

If the same component meets the new attaching interface at k, the
last-block M-coset invariant gives a concrete shift u ∈ K_(M∩A)
satisfying g·incl(u) = h·i(k). This is not a new hypothesis.

The normalized noncommutative Link squares then promote this single
equation to every parameter of the genuine common triple-mask group
K_(M∩A∩B), as an equality of points in the *literal extension
pushout* of the entire old chain and its next Cayley block.

This is the geometric boundary alignment needed to extend the
normalized smaller-mask chart through arbitrary finite histories.
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

/-- When an old whole-chain M-component meets both the previous
last block at g and the new interface at k, the actual earlier
K_(M∩A) inclusion gives a normalized shift aligning those points.
No commutativity or normality is used. -/
theorem step_normalizedShift_exists
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space)
    (g : (old R.current.1).Carrier)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hqg : LabelReach
      (fun e => (R.state.matching e).Rel) M.val q (R.state.lastEmbed g))
    (hqk : LabelReach
      (fun e => (R.state.matching e).Rel) M.val q
      (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 k))) :
    ∃ shift : (old (Step.meet S M R.current.1)).Carrier,
      g * (L (Step.meet S M R.current.1) R.current.1
        Finset.inter_subset_right).incl shift =
        R.current.2 * left D S old L R.current.1 y.1 k := by
  let i := left D S old L R.current.1 y.1
  let p := (L (Step.meet S M R.current.1) R.current.1
    Finset.inter_subset_right).incl
  have hreach : LabelReach
      (fun e => (R.state.matching e).Rel) M.val
      (R.state.lastEmbed g)
      (R.state.lastEmbed (R.current.2 * i k)) :=
    LabelReach.trans (LabelReach.symm hqg) hqk
  have hcoset := (hprev g (R.current.2 * i k)).mp hreach
  change g⁻¹ * (R.current.2 * i k) ∈ p.range at hcoset
  obtain ⟨shift, hshift⟩ := hcoset
  refine ⟨shift, ?_⟩
  change g * p shift = R.current.2 * i k
  calc
    g * p shift = g * (g⁻¹ * (R.current.2 * i k)) := by rw [hshift]
    _ = R.current.2 * i k := by group

/-- One shift aligns the *entire* normalized triple-mask interface
in the genuine extension of the existing old chain. The left
coordinate lies in the actual preceding last embedded Cayley block,
while the right coordinate is in the newly attached block.

This is a statement inside the literal SetPushout, not merely
in the isolated two-block group attachment. -/
theorem step_normalizedBoundary_all
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space)
    (g : (old R.current.1).Carrier)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hqg : LabelReach
      (fun e => (R.state.matching e).Rel) M.val q (R.state.lastEmbed g))
    (hqk : LabelReach
      (fun e => (R.state.matching e).Rel) M.val q
      (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 k))) :
    let A := R.current.1
    let B := y.1
    let i := left D S old L A B
    let j := right D S old L A B
    let f := attachInto R.state.lastEmbed R.current.2 i
    let hf := attachInto_injective
      R.state.lastEmbed R.state.lastInjective R.current.2 i
      (left_injective D S old L A B)
    let hj := right_injective D S old L A B
    ∃ shift : (old (Step.meet S M A)).Carrier,
      ∀ t : (old (Step.meet S M (common S A B))).Carrier,
      pushoutInl f j hf hj
        (R.state.lastEmbed
          (g * (L (Step.meet S M A) A
            Finset.inter_subset_right).incl
            (shift * normalizedCommonLeft D S old L M A B t))) =
      pushoutInr f j hf hj
        ((j k) *
          (L (Step.meet S M B) B Finset.inter_subset_right).incl
            (normalizedCommonRight D S old L M A B t)) := by
  let A := R.current.1
  let B := y.1
  let i := left D S old L A B
  let j := right D S old L A B
  let p := (L (Step.meet S M A) A Finset.inter_subset_right).incl
  let s := (L (Step.meet S M B) B Finset.inter_subset_right).incl
  let r := normalizedCommonInterface D S old L M A B
  let a := normalizedCommonLeft D S old L M A B
  let b := normalizedCommonRight D S old L M A B
  let f := attachInto R.state.lastEmbed R.current.2 i
  let hf := attachInto_injective
    R.state.lastEmbed R.state.lastInjective R.current.2 i
    (left_injective D S old L A B)
  let hj := right_injective D S old L A B
  obtain ⟨shift, hbase⟩ :=
    step_normalizedShift_exists D S old L M R y hprev q g k hqg hqk
  refine ⟨shift, ?_⟩
  intro t
  have hOld := normalized_old_boundary i p r a
    (normalizedCommon_left_square D S old L M A B)
    g R.current.2 k shift hbase t
  have hNew := normalized_new_boundary j s r b
    (normalizedCommon_right_square D S old L M A B) k t
  change
    pushoutInl f j hf hj
      (R.state.lastEmbed (g * p (shift * a t))) =
    pushoutInr f j hf hj ((j k) * s (b t))
  calc
    pushoutInl f j hf hj
        (R.state.lastEmbed (g * p (shift * a t))) =
      pushoutInl f j hf hj
        (R.state.lastEmbed (R.current.2 * i (k * r t))) := by rw [hOld]
    _ = pushoutInr f j hf hj (j (k * r t)) :=
      pushout_attachment f j hf hj (k * r t)
    _ = pushoutInr f j hf hj ((j k) * s (b t)) := by rw [hNew]

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
