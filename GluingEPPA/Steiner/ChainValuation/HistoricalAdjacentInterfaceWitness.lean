import GluingEPPA.Steiner.ChainValuation.ExactCrossLayerWitness
import GluingEPPA.Steiner.ChainValuation.HistoricalBlockFamily

/-!
# Actual interface witnesses for adjacent active historical pieces

A component's historical support is an interval, but an interval
alone does not identify the attaching parameter between consecutive
active pieces. The following lemmas supply the missing *witness*.

Whenever a component of a true separated chain extension meets
an old historical Cayley chart and also the new Cayley block,
there is a parameter k in the **genuine common attaching group**
such that the selected old chart point reaches the old image of k
and the selected new point reaches the new image of k.

The second theorem states this directly for the two consecutive
historical blocks at the manuscript's LinkChain.step. These are
statements about true labelled paths, not graph-theoretic guesses
or an extra "connected attachment" assumption.

Global bookkeeping of the witnesses across a full finite history
remains to be done.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {K : Type v} [Group K]

/-- If one M-component of a genuine extension meets an old
historical chart and the newly attached group, then there is
a real attachment parameter joining the selected points by
M-paths on the two respective sides. -/
theorem historicalBlock_newBlock_common_interface_witness
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier) (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E)
    (hpull : AttachmentReachCompatible A B C h left right M)
    (T : HistoricalBlock A C M)
    (q : (extend A B C h left right hl hr hsep hshared).Space)
    (hOld : ∃ x : T.Carrier,
      LabelReach
        (fun e => ((extend A B C h left right hl hr
          hsep hshared).matching e).Rel) M q
        (oldEmbed A B C h left right hl hr (T.chart.embed x)))
    (hNew : ∃ y : B.Carrier,
      LabelReach
        (fun e => ((extend A B C h left right hl hr
          hsep hshared).matching e).Rel) M q
        (newEmbed A B C h left right hl hr y)) :
    ∃ k : K, ∃ x : T.Carrier, ∃ y : B.Carrier,
      LabelReach (fun e => (C.matching e).Rel) M
        (T.chart.embed x) (attachInto C.lastEmbed h left k) ∧
      LabelReach (fun e => (B.matching e).Rel) M
        (right k) y ∧
      LabelReach
        (fun e => ((extend A B C h left right hl hr
          hsep hshared).matching e).Rel) M q
        (oldEmbed A B C h left right hl hr (T.chart.embed x)) ∧
      LabelReach
        (fun e => ((extend A B C h left right hl hr
          hsep hshared).matching e).Rel) M q
        (newEmbed A B C h left right hl hr y) := by
  obtain ⟨x, hx⟩ := hOld
  obtain ⟨y, hy⟩ := hNew
  have hxy :
      LabelReach
        (fun e => ((extend A B C h left right hl hr
          hsep hshared).matching e).Rel) M
        (oldEmbed A B C h left right hl hr (T.chart.embed x))
        (newEmbed A B C h left right hl hr y) :=
    LabelReach.trans (LabelReach.symm hx) hy
  obtain ⟨k, hleft, hright⟩ :=
    (extend_cross_reach_iff_attachment
      A B C h left right hl hr hsep hshared M hpull
      (T.chart.embed x) y).mp hxy
  exact ⟨k, x, y, hleft, hright, hx, hy⟩

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

/-- If the M-component of a point in the real LinkChain.step
meets the *previous last Cayley block* as well as the new one,
the two selected pieces are joined by a genuine parameter
k∈K_(A∩B). The old-side path is in the entire old chain, not
necessarily in a single group. -/
theorem step_previous_new_common_interface_witness
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (q : (step D S old L R y hsep).state.Space)
    (hOld : ∃ g : (old R.current.1).Carrier,
      LabelReach
        (fun e => ((step D S old L R y hsep).state.matching e).Rel)
        M.val q
        (oldEmbed (block S old R.current.1) (block S old y.1)
          R.state R.current.2
          (left D S old L R.current.1 y.1)
          (right D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1)
          (right_injective D S old L R.current.1 y.1)
          (R.state.lastEmbed g)))
    (hNew : ∃ z : (old y.1).Carrier,
      LabelReach
        (fun e => ((step D S old L R y hsep).state.matching e).Rel)
        M.val q
        (newEmbed (block S old R.current.1) (block S old y.1)
          R.state R.current.2
          (left D S old L R.current.1 y.1)
          (right D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1)
          (right_injective D S old L R.current.1 y.1) z)) :
    ∃ k : (old (common S R.current.1 y.1)).Carrier,
      ∃ g : (old R.current.1).Carrier,
      ∃ z : (old y.1).Carrier,
        LabelReach (fun e => (R.state.matching e).Rel) M.val
          (R.state.lastEmbed g)
          (R.state.lastEmbed
            (R.current.2 * left D S old L R.current.1 y.1 k)) ∧
        LabelReach
          (fun e => ((block S old y.1).matching e).Rel)
          M.val (right D S old L R.current.1 y.1 k) z := by
  obtain ⟨g, hg⟩ := hOld
  obtain ⟨z, hz⟩ := hNew
  have hcross :
      LabelReach
        (fun e => ((step D S old L R y hsep).state.matching e).Rel)
        M.val
        (oldEmbed (block S old R.current.1) (block S old y.1)
          R.state R.current.2
          (left D S old L R.current.1 y.1)
          (right D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1)
          (right_injective D S old L R.current.1 y.1)
          (R.state.lastEmbed g))
        (newEmbed (block S old R.current.1) (block S old y.1)
          R.state R.current.2
          (left D S old L R.current.1 y.1)
          (right D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1)
          (right_injective D S old L R.current.1 y.1) z) :=
    LabelReach.trans (LabelReach.symm hg) hz
  obtain ⟨k, hkOld, hkNew⟩ :=
    (step_cross_reach_iff_attachment D S old L
      M R y hsep hprev (R.state.lastEmbed g) z).mp hcross
  exact ⟨k, g, z, hkOld, hkNew⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
