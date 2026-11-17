import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelBuild
import GluingEPPA.Steiner.ChainValuation.ChainTests

/-!
# Relabel the actual bounded-chain test package

The indexed test uses the literal builder on List.ofFn of a raw chain.
The preceding buildNonempty theorem is transported through that exact
finite index (including the unused last-shift coordinate).

This stage is conditional on earlier-stage RelabelData: construction of
that input from an actual diagram isomorphism remains separate.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData

universe u
variable {V E V' E' : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (D' : EdgeGraph V' E') [Finite V'] [Fintype E'] [DecidableEq E']
variable (S : Finset E) (T : Finset E')
variable (old : ∀ i : Proper S, Data E i.val)
variable (old' : ∀ i : Proper T, Data E' i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))
variable (L' : ∀ m t : Proper T, m.val ⊆ t.val → Link D' (old' m) (old' t))
variable {p : E ≃ E'}

/-- The exact test indexed by a separated bounded raw chain has an
edge-reflecting equivalence to its relabelled actual target test. -/
theorem chainSpace_matchingRelabel
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) (c : SeparatedChains D N S old L) :
    ∃ F :
      chainSpace D N S old L c ≃
        chainSpace D' N T old' L'
          (chainIndexEquiv D D' S T old old' L L' R N c),
      ∀ e u v,
        ((chainState D N S old L c).state.matching e).Rel u v ↔
        ((chainState D' N T old' L'
          (chainIndexEquiv D D' S T old old' L L' R N c)).state.matching (p e)).Rel
          (F u) (F v) := by
  let c' := chainIndexEquiv D D' S T old old' L L' R N c
  have hl : List.ofFn c'.1.2 =
      (List.ofFn c.1.2).map (atomEquiv D D' S T old old' L L' R) := by
    dsimp [c', chainIndexEquiv]
    exact rawRelabel_list D D' S T old old' L L' R N c.1
  have h := buildNonempty_matchingRelabel D D' S T old old' L L' R
    (List.ofFn c.1.2) (rawChain_list_nonempty N S old c.1) c.2
  rw [← hl] at h
  simpa only [chainSpace, chainState, c'] using h

/-- With the genuine edge relation transported, the canonical involutive
fixed-point completion of every named edge is transported as well. -/
theorem chainPerm_equivariant
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) (c : SeparatedChains D N S old L) :
    ∃ F :
      chainSpace D N S old L c ≃
        chainSpace D' N T old' L'
          (chainIndexEquiv D D' S T old old' L L' R N c),
      ∀ e x,
        F (chainPerm D N S old L c e x) =
          chainPerm D' N T old' L'
            (chainIndexEquiv D D' S T old old' L L' R N c)
            (p e) (F x) := by
  obtain ⟨F,hrel⟩ := chainSpace_matchingRelabel D D' S T old old' L L' R N c
  refine ⟨F,?_⟩
  intro e x
  exact ChainValuation.matching_perm_conjugate_of_rel_iff F
    ((chainState D N S old L c).state.matching e)
    ((chainState D' N T old' L'
      (chainIndexEquiv D D' S T old old' L L' R N c)).state.matching (p e))
    (hrel e) x

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
