import GluingEPPA.Steiner.ChainValuation.HistoricalAdjacentInterfaceWitness
import GluingEPPA.Steiner.ChainValuation.LinkCayleyMask

/-!
# Genuine Cayley-block paths witness adjacent Link interfaces

The exact cross-layer theorem identifies the attaching parameter
where a path between the old chain and new block crosses.

For the *two actual consecutive Cayley blocks* A and B, more is true:
if the old endpoint belongs to the last Cayley block K_A, the
last-block coset invariant reflects its whole-chain M-path to
the attachment into an M-path inside the genuine K_A Cayley graph.
Thus the witness consists of:
- an old-block M-path in K_A from g to h·i(k);
- a new-block M-path in K_B from j(k) to z;
- the true parameter k∈K_(A∩B).

This is the exact local adjacency criterion needed to retain
boundary witnesses through subsequent chain extensions.
No outside path or ambient full-stage K_S is assumed.
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

/-- For the literal consecutive block charts of LinkChain.step, a
genuine cross-block M-path exists exactly when it factors across
the true earlier Link interface, by *internal* M-paths in each
of the two Cayley blocks. -/
theorem step_adjacentCayley_reach_iff_interface
    (M : Proper S) (R : BuildResult D S old L)
    (y : Atom S old)
    (hsep :
      match R.previous with
      | none => True
      | some p => tripleSeparated D S old L p R.current y)
    (hprev : LastMaskCoset D S old L M R)
    (g : (old R.current.1).Carrier)
    (z : (old y.1).Carrier) :
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
        (right_injective D S old L R.current.1 y.1) z) ↔
    ∃ k : (old (common S R.current.1 y.1)).Carrier,
      LabelReach
        (fun e => ((block S old R.current.1).matching e).Rel)
        M.val g
        (R.current.2 * left D S old L R.current.1 y.1 k) ∧
      LabelReach
        (fun e => ((block S old y.1).matching e).Rel)
        M.val (right D S old L R.current.1 y.1 k) z := by
  let i := left D S old L R.current.1 y.1
  let j := right D S old L R.current.1 y.1
  constructor
  · intro hcross
    obtain ⟨k, hOld, hNew⟩ :=
      (step_cross_reach_iff_attachment
        D S old L M R y hsep hprev
        (R.state.lastEmbed g) z).mp hcross
    have hcoset :
        R.current.2 * i k ∈
          leftCoset (restrictedSubgroup D S old L M R.current.1) g :=
      (hprev g (R.current.2 * i k)).mp hOld
    have hblock :
        LabelReach
          (fun e => ((block S old R.current.1).matching e).Rel)
          M.val g (R.current.2 * i k) :=
      (restricted_block_reach_iff_coset D S old L
        M R.current.1 g (R.current.2 * i k)).mpr hcoset
    exact ⟨k, hblock, hNew⟩
  · rintro ⟨k, hOld, hNew⟩
    have hcoset :
        R.current.2 * i k ∈
          leftCoset (restrictedSubgroup D S old L M R.current.1) g :=
      (restricted_block_reach_iff_coset D S old L
        M R.current.1 g (R.current.2 * i k)).mp hOld
    have hWhole :
        LabelReach (fun e => (R.state.matching e).Rel) M.val
          (R.state.lastEmbed g)
          (R.state.lastEmbed (R.current.2 * i k)) :=
      (hprev g (R.current.2 * i k)).mpr hcoset
    exact (step_cross_reach_iff_attachment
      D S old L M R y hsep hprev
      (R.state.lastEmbed g) z).mpr ⟨k, hWhole, hNew⟩

/-- In particular, whenever a real M-component meets *both* of
the last two historical blocks, its chosen points admit an
interface witness with M-paths in those very Cayley groups.

The component root q is arbitrary in the extended quotient;
it need not belong to either historical block. -/
theorem step_adjacentCayley_meets_witness
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
      LabelReach
        (fun e => ((block S old R.current.1).matching e).Rel)
        M.val g
        (R.current.2 * left D S old L R.current.1 y.1 k) ∧
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
  obtain ⟨k, hA, hB⟩ :=
    (step_adjacentCayley_reach_iff_interface
      D S old L M R y hsep hprev g z).mp hcross
  exact ⟨k, g, z, hA, hB⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
