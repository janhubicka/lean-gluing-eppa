import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelStep

/-!
# Naturality of the actual first two-block chain

The first actual Cayley block has an edge-reflecting equivalence;
attaching its second block gives an exact pushout equivalence.
The first attachment has empty entry and needs no further separation.
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

/-- The concrete two-block PairResult carries the relabelled
edge-reflecting quotient equivalence. -/
noncomputable def pairState
    (R : RelabelData D D' S T old old' L L' p)
    (x y : Atom S old) :
    ChainValuation.StateRelabel p (R.stage y.1)
      (pair D S old L x y).state
      (pair D' T old' L'
        ((atomEquiv D D' S T old old' L L' R) x)
        ((atomEquiv D D' S T old old' L L' R) y)).state := by
  have hsep :
      Disjoint (ChainValuation.ChainState.first (block S old x.1)).entry
        (ChainValuation.exitSet (block S old x.1) x.2
          (left D S old L x.1 y.1)) := by
    simp [ChainValuation.ChainState.first]
  have hfirst := firstState D D' S T old old' L L' R x.1
  have hext := extendState D D' S T old old' L L' R x.1 y.1
    (ChainValuation.ChainState.first (block S old x.1))
    (ChainValuation.ChainState.first (block T old' (R.proper x.1)))
    hfirst x.2 hsep
  exact hext

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
