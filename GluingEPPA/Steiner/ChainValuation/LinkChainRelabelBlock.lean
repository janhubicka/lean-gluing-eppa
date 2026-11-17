import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelData
import GluingEPPA.Steiner.ChainValuation.StateRelabelWord

/-!
# Naturality of the first actual LinkChain block

The group and edge data in RelabelData give an equivalence of the exact
initial Cayley block and its fixed-point-completed letter matchings.
Together with the one-attachment extension lemma, this supplies the base
case for induction along the literal finite chain builder.
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

/-- The literal first-block states are canonically edge-reflecting under
the old-stage isomorphisms in the relabelling data. -/
noncomputable def firstState
    (R : RelabelData D D' S T old old' L L' p)
    (i : Proper S) :
    ChainValuation.StateRelabel p (R.stage i)
      (ChainValuation.ChainState.first (block S old i))
      (ChainValuation.ChainState.first (block T old' (R.proper i))) :=
  ChainValuation.StateRelabel.initial
    (block S old i) (block T old' (R.proper i))
    p (R.stage i) (R.active i) (R.edge i)

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
