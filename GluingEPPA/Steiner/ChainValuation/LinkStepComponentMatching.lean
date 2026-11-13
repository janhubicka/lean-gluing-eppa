import GluingEPPA.Steiner.ChainValuation.LinkStepCoset
import GluingEPPA.Steiner.ChainValuation.ChainComponentPullback

/-!
# Component matchings at the actual LinkChain.step

For an actual separated chain prefix satisfying its checked
last-block M-coset invariant, the earlier Link subgroup pullback
identity *proves* the compatibility needed for the generic
matching-gluing theorem. In particular the matching of true old-
chain and new-block M-components is a genuine partial matching.

The last theorem identifies literal M-coloured reachability in
LinkChain.step with the quotient of this matching. No hypothesis
about a hypothetical completed K_S is used.

This is one induction step, not yet the global interval/coset
normal form for the whole finite chain.
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

/-- The actual earlier-stage Link pullback equality discharges all
the assumptions of M-reachability compatibility at an attachment
to a separated chain prefix. -/
theorem step_attachment_compatible
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hprev : LastMaskCoset D S old L M R) :
    AttachmentReachCompatible
      (block S old R.current.1) (block S old y.1)
      R.state R.current.2
      (left D S old L R.current.1 y.1)
      (right D S old L R.current.1 y.1)
      M.val := by
  exact attachment_compatible_of_cosets
    (block S old R.current.1) (block S old y.1)
    R.state R.current.2
    (left D S old L R.current.1 y.1)
    (right D S old L R.current.1 y.1)
    M.val
    (restrictedSubgroup D S old L M R.current.1)
    (restrictedSubgroup D S old L M y.1)
    (restrictedSubgroup_pullback D S old L M R.current.1 y.1)
    hprev
    (restricted_block_reach_iff_coset D S old L M y.1)

/-- The actual matching of old-chain and new-block quotient
M-components, with the pullback witness obtained from
earlier-stage Links and the checked last-block invariant. -/
noncomputable def stepComponentMatching
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hprev : LastMaskCoset D S old L M R) :
    Matching
      (Sum
        (Quotient (labelReachSetoid
          (fun e => (R.state.matching e).Rel) M.val))
        (Quotient (labelReachSetoid
          (fun e => ((block S old y.1).matching e).Rel) M.val))) :=
  canonicalAttachmentMatching
    (labelReachSetoid (fun e => (R.state.matching e).Rel) M.val)
    (labelReachSetoid
      (fun e => ((block S old y.1).matching e).Rel) M.val)
    (attachInto R.state.lastEmbed R.current.2
      (left D S old L R.current.1 y.1))
    (right D S old L R.current.1 y.1)
    (step_attachment_compatible D S old L M R y hprev)

/-- At the manuscript's literal LinkChain.step, actual M-path
connectivity is exactly the canonical partial matching quotient.
All compatibility assumptions are discharged by earlier Link
identities, the preceding last-block coset invariant and separation. -/
theorem step_reach_iff_componentMatching
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (a b : Sum R.state.Space (old y.1).Carrier) :
    LabelReach
      (fun e => ((step D S old L R y hsep).state.matching e).Rel)
      M.val
      (pushoutPoint
        (attachInto R.state.lastEmbed R.current.2
          (left D S old L R.current.1 y.1))
        (right D S old L R.current.1 y.1)
        (attachInto_injective
          R.state.lastEmbed R.state.lastInjective R.current.2
          (left D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1))
        (right_injective D S old L R.current.1 y.1) a)
      (pushoutPoint
        (attachInto R.state.lastEmbed R.current.2
          (left D S old L R.current.1 y.1))
        (right D S old L R.current.1 y.1)
        (attachInto_injective
          R.state.lastEmbed R.state.lastInjective R.current.2
          (left D S old L R.current.1 y.1)
          (left_injective D S old L R.current.1 y.1))
        (right_injective D S old L R.current.1 y.1) b) ↔
    componentClass
        (labelReachSetoid (fun e => (R.state.matching e).Rel) M.val)
        (labelReachSetoid
          (fun e => ((block S old y.1).matching e).Rel) M.val)
        (stepComponentMatching D S old L M R y hprev) a =
    componentClass
        (labelReachSetoid (fun e => (R.state.matching e).Rel) M.val)
        (labelReachSetoid
          (fun e => ((block S old y.1).matching e).Rel) M.val)
        (stepComponentMatching D S old L M R y hprev) b := by
  have hd := step_attachment_disjoint D S old L R y hsep
  have hs : ∀ e, e ∈ (block S old R.current.1).active →
      e ∈ (block S old y.1).active →
      ∃ k : (old (common S R.current.1 y.1)).Carrier,
        left D S old L R.current.1 y.1 k =
          (block S old R.current.1).edge e ∧
        right D S old L R.current.1 y.1 k =
          (block S old y.1).edge e := by
    intro e ha hb
    exact shared_edge D S old L R.current.1 y.1 e ha hb
  exact chainExtend_reach_iff_component_matching
    (block S old R.current.1) (block S old y.1)
    R.state R.current.2
    (left D S old L R.current.1 y.1)
    (right D S old L R.current.1 y.1)
    (left_injective D S old L R.current.1 y.1)
    (right_injective D S old L R.current.1 y.1)
    hd hs M.val
    (step_attachment_compatible D S old L M R y hprev) a b

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
