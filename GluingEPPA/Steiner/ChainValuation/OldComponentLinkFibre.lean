import GluingEPPA.Steiner.ChainValuation.LinkStepCoset
import GluingEPPA.Steiner.ChainValuation.LinkAttachmentFibers

/-!
# Exact Link fibre for an M-component of the *entire old chain*

When attaching a new earlier Cayley block, the old piece is an actual
M-connected component of the whole already constructed chain, not
merely a coset in the last block. The checked last-block coset
invariant and Link fibre theorem show that an old component which
meets the attachment at parameter k selects **exactly** the same
attaching parameters as the restricted new-block coset through j(k).

This bridges the genuine old-chain components to the literal
matched-restriction condition required by exact pushout geometry,
without postulating a new compatibility or ambient-group axiom.
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

/-- A genuine M-component of any chain state is closed under the
actual named M-edges of that state. -/
theorem oldComponent_mask_edge_closed
    (M : Finset E) (R : BuildResult D S old L)
    (q x y : R.state.Space) (e : E)
    (he : e ∈ M)
    (hx : LabelReach (fun e => (R.state.matching e).Rel) M q x)
    (hxy : (R.state.matching e).Rel x y) :
    LabelReach (fun e => (R.state.matching e).Rel) M q y :=
  LabelReach.trans hx (LabelReach.edge e he hxy)

/-- The full old M-component and the new M-restricted coset
have exactly the same preimage in the actual common Link group.
The hypothesis hq just chooses the old component's interface
base point k; all other attaching points are then determined. -/
theorem step_oldComponent_attachment_fibre_iff
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hprev : LastMaskCoset D S old L M R)
    (q : R.state.Space)
    (k : (old (common S R.current.1 y.1)).Carrier)
    (hq : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 k)))
    (z : (old (common S R.current.1 y.1)).Carrier) :
    LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (R.state.lastEmbed
        (R.current.2 * left D S old L R.current.1 y.1 z)) ↔
    right D S old L R.current.1 y.1 z ∈
      leftCoset
        (restrictedSubgroup D S old L M y.1)
        (right D S old L R.current.1 y.1 k) := by
  have hshift :
      LabelReach (fun e => (R.state.matching e).Rel) M.val
        q (R.state.lastEmbed
          (R.current.2 * left D S old L R.current.1 y.1 z)) ↔
      LabelReach (fun e => (R.state.matching e).Rel) M.val
        (R.state.lastEmbed
          (R.current.2 * left D S old L R.current.1 y.1 k))
        (R.state.lastEmbed
          (R.current.2 * left D S old L R.current.1 y.1 z)) := by
    constructor
    · intro hz
      exact LabelReach.trans (LabelReach.symm hq) hz
    · intro hkz
      exact LabelReach.trans hq hkz
  exact hshift.trans
    ((hprev
      (R.current.2 * left D S old L R.current.1 y.1 k)
      (R.current.2 * left D S old L R.current.1 y.1 z)).trans
      (restrictedLink_fibre_mem_iff D S old L
        M R.current.1 y.1 R.current.2 k z))

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
