import GluingEPPA.Steiner.ChainValuation.CanonicalAttachmentMatching
import GluingEPPA.Steiner.ChainValuation.ChainAttachReach
import GluingEPPA.Steiner.ChainValuation.LinkStepComponentMatching

/-!
# Exact witnesses for crossing one genuine attachment interface

The matching quotient proves that the only way an old occurrence
and a new occurrence can belong to the same M-component of an
injective labelled pushout is through a *real attaching parameter*.

We extract this parameter explicitly in both directions: the
selected old point reaches f(k) using only old M-edges, and g(k)
reaches the new point using only new M-edges. This is stronger than
saying the glued component meets both sides, and is the missing
geometric witness for normalization across adjacent chain blocks.

The second theorem specializes the result to the exact manuscript
LinkChain.step using the earlier-stage Link pullback identity.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v w t
variable {E : Type u} {X : Type v} {Y : Type w} {Z : Type t}

/-- A cross-side M-path in the *literal* quotient exists if and only
if one actual attachment parameter joins the corresponding old and
new M-components. Multiple crossings cannot create a new connection. -/
theorem pushout_cross_reach_iff_attachment
    (R : E → X → X → Prop) (T : E → Y → Y → Prop)
    (M : Finset E) (f : Z → X) (g : Z → Y)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hpull : ∀ z z' : Z,
      LabelReach R M (f z) (f z') ↔
      LabelReach T M (g z) (g z'))
    (x : X) (y : Y) :
    LabelReach (pushoutLabelRel R T f g hf hg) M
      (pushoutInl f g hf hg x) (pushoutInr f g hf hg y) ↔
    ∃ z : Z, LabelReach R M x (f z) ∧
      LabelReach T M (g z) y := by
  let RX := labelReachSetoid R M
  let RY := labelReachSetoid T M
  let P := canonicalAttachmentMatching RX RY f g hpull
  constructor
  · intro hxy
    have hglued : GluedReach RX RY f g (.inl x) (.inr y) :=
      (pushoutReach_iff_gluedReach R T M f g hf hg
        (.inl x) (.inr y)).mp hxy
    have heq :
        componentClass RX RY P (.inl x) =
          componentClass RX RY P (.inr y) :=
      (gluedReach_iff_canonical_matching RX RY f g hpull
        (.inl x) (.inr y)).mp hglued
    have hpair := (P.quotient_eq_iff
        (Sum.inl (Quotient.mk RX x))
        (Sum.inr (Quotient.mk RY y))).mp heq
    rcases hpair with hsame | hmatch
    · cases hsame
    · change AttachmentComponentPair RX RY f g
        (Quotient.mk RX x) (Quotient.mk RY y) at hmatch
      obtain ⟨z, hzX, hzY⟩ := hmatch
      exact ⟨z, Quotient.exact hzX.symm, Quotient.exact hzY⟩
  · rintro ⟨z, hx, hy⟩
    exact gluedReach_to_pushoutReach R T M f g hf hg
      (GluedReach.trans (GluedReach.old hx)
        (GluedReach.trans (GluedReach.attach z)
          (GluedReach.new hy)))

/-- The same exact cross-layer witness in the true completed
matching of a separated ChainState.extend. The gluing relation
here is not an auxiliary model of the quotient. -/
theorem extend_cross_reach_iff_attachment
    {K : Type t} [Group K]
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (x : C.Space) (y : B.Carrier) :
    LabelReach
      (fun e => ((extend A B C h left right hl hr
        hsep hshared).matching e).Rel) M
      (oldEmbed A B C h left right hl hr x)
      (newEmbed A B C h left right hl hr y) ↔
    ∃ k : K,
      LabelReach (fun e => (C.matching e).Rel) M
        x (attachInto C.lastEmbed h left k) ∧
      LabelReach (fun e => (B.matching e).Rel) M (right k) y := by
  rw [chainState_extend_reach_iff_glued
    A B C h left right hl hr hsep hshared M (.inl x) (.inr y)]
  constructor
  · intro hxy
    let RX := labelReachSetoid (fun e => (C.matching e).Rel) M
    let RY := labelReachSetoid (fun e => (B.matching e).Rel) M
    let f := attachInto C.lastEmbed h left
    let P := canonicalAttachmentMatching RX RY f right hpull
    have heq :
        componentClass RX RY P (.inl x) =
          componentClass RX RY P (.inr y) :=
      (gluedReach_iff_canonical_matching RX RY f right hpull
        (.inl x) (.inr y)).mp hxy
    have hpair := (P.quotient_eq_iff
        (Sum.inl (Quotient.mk RX x))
        (Sum.inr (Quotient.mk RY y))).mp heq
    rcases hpair with hsame | hmatch
    · cases hsame
    · change AttachmentComponentPair RX RY f right
        (Quotient.mk RX x) (Quotient.mk RY y) at hmatch
      obtain ⟨k, hkX, hkY⟩ := hmatch
      exact ⟨k, Quotient.exact hkX.symm, Quotient.exact hkY⟩
  · rintro ⟨k, hx, hy⟩
    exact GluedReach.trans (GluedReach.old hx)
      (GluedReach.trans (GluedReach.attach k)
        (GluedReach.new hy))

end GluingEPPA.Steiner.ChainValuation

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

/-- Every real M-path across a manuscript LinkChain.step has a
witness in the *actual* earlier intersection group K_(A∩B).
The intermediate paths stay respectively in the whole old chain
and the newly attached Cayley group, as required for the
normalized component-chart induction. -/
theorem step_cross_reach_iff_attachment
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (x : R.state.Space) (z : (old y.1).Carrier) :
    LabelReach
      (fun e => ((step D S old L R y hsep).state.matching e).Rel)
      M.val
      (oldEmbed (block S old R.current.1) (block S old y.1)
        R.state R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1) x)
      (newEmbed (block S old R.current.1) (block S old y.1)
        R.state R.current.2
        (left D S old L R.current.1 y.1)
        (right D S old L R.current.1 y.1)
        (left_injective D S old L R.current.1 y.1)
        (right_injective D S old L R.current.1 y.1) z) ↔
    ∃ k : (old (common S R.current.1 y.1)).Carrier,
      LabelReach (fun e => (R.state.matching e).Rel) M.val
        x (R.state.lastEmbed
          (R.current.2 * left D S old L R.current.1 y.1 k)) ∧
      LabelReach (fun e => ((block S old y.1).matching e).Rel)
        M.val (right D S old L R.current.1 y.1 k) z := by
  let A := block S old R.current.1
  let B := block S old y.1
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  have hi := left_injective D S old L R.current.1 y.1
  have hj := right_injective D S old L R.current.1 y.1
  have hd := step_attachment_disjoint D S old L R y hsep
  have hs : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : (old (common S R.current.1 y.1)).Carrier,
        i k = A.edge e ∧ j k = B.edge e := by
    intro e ha hb
    exact shared_edge D S old L R.current.1 y.1 e ha hb
  have hpull := step_attachment_compatible D S old L M R y hprev
  change LabelReach
      (fun e => ((extend A B R.state R.current.2 i j
        hi hj hd hs).matching e).Rel) M.val
      (oldEmbed A B R.state R.current.2 i j hi hj x)
      (newEmbed A B R.state R.current.2 i j hi hj z) ↔
    ∃ k : (old (common S R.current.1 y.1)).Carrier,
      LabelReach (fun e => (R.state.matching e).Rel)
        M.val x (attachInto R.state.lastEmbed R.current.2 i k) ∧
      LabelReach (fun e => (B.matching e).Rel) M.val (j k) z
  exact extend_cross_reach_iff_attachment
    A B R.state R.current.2 i j hi hj hd hs M.val hpull x z

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
