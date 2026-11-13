import GluingEPPA.Steiner.ChainValuation.LinkLastCoset

/-!
# The M-coset invariant for the manuscript's literal BuildResult.step

The previous lemma works for an arbitrary true separated ChainState.extend.
This file identifies its separation argument with exactly the
`LinkChain.step` construction from the manuscript. The verified
initial state and one step preserve the last-block coset property.

The subsequent finite-list `buildNonempty` induction and the normalized
smaller-chain test charts are deliberately separate.
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

/-- The one-step internal separation used by the actual existing
`LinkChain.step`, extracted as a reusable named theorem. -/
theorem step_attachment_disjoint
    (R : BuildResult D S old L) (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y) :
    Disjoint R.state.entry
      (GluingEPPA.Steiner.ChainValuation.exitSet
        (block S old R.current.1) R.current.2
        (left D S old L R.current.1 y.1)) := by
  cases hp : R.previous with
  | none =>
      have he : R.state.entry = ∅ := by
        simpa [hp] using R.entry_spec
      simp [he]
  | some p =>
      have he : R.state.entry =
          Set.range (right D S old L p.1 R.current.1) := by
        simpa [hp] using R.entry_spec
      have hs : tripleSeparated D S old L p R.current y := by
        simpa [hp] using hsep
      change Disjoint
        (GluingEPPA.Steiner.ChainValuation.leftCoset
          (right D S old L p.1 R.current.1).range 1)
        (GluingEPPA.Steiner.ChainValuation.leftCoset
          (left D S old L R.current.1 y.1).range R.current.2) at hs
      have hentry : Set.range (right D S old L p.1 R.current.1) =
          GluingEPPA.Steiner.ChainValuation.leftCoset
            (right D S old L p.1 R.current.1).range 1 :=
        GluingEPPA.Steiner.ChainValuation.range_eq_leftCoset_one _
      have hexit :
          GluingEPPA.Steiner.ChainValuation.exitSet
              (block S old R.current.1) R.current.2
              (left D S old L R.current.1 y.1) =
          GluingEPPA.Steiner.ChainValuation.leftCoset
            (left D S old L R.current.1 y.1).range R.current.2 :=
        GluingEPPA.Steiner.ChainValuation.translated_range_eq_leftCoset
          (left D S old L R.current.1 y.1) R.current.2
      rw [he, hentry, hexit]
      exact hs

/-- The last-block M-coset statement as a property of the literal
partially built chain, not an independently chosen chain model. -/
def LastMaskCoset (M : Proper S) (R : BuildResult D S old L) : Prop :=
  GluingEPPA.Steiner.ChainValuation.LastBlockCosetInvariant
    (block S old R.current.1) R.state M.val
    (restrictedSubgroup D S old L M R.current.1)

/-- Base case: a single true earlier Cayley group. -/
theorem initial_lastMaskCoset (M : Proper S) (x : Atom S old) :
    LastMaskCoset D S old L M (initial D S old L x) := by
  intro a b
  change GluingEPPA.Steiner.ChainValuation.LabelReach
      (fun e => ((block S old x.1).matching e).Rel) M.val a b ↔
    b ∈ GluingEPPA.Steiner.ChainValuation.leftCoset
      (L (Step.meet S M x.1) x.1 Finset.inter_subset_right).incl.range a
  exact restricted_block_reach_iff_coset D S old L M x.1 a b

/-- One existing chain-building step preserves the invariant.
This is the direct instantiation for `LinkChain.step`. -/
theorem step_lastMaskCoset
    (M : Proper S) (R : BuildResult D S old L) (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R) :
    LastMaskCoset D S old L M (step D S old L R y hsep) := by
  have hd := step_attachment_disjoint D S old L R y hsep
  have hnew := link_extend_lastCoset D S old L
    M R.current.1 y.1 R.state R.current.2 hd hprev
  exact hnew

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
