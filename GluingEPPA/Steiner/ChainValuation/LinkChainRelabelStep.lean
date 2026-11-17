import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelBlock
import GluingEPPA.Steiner.ChainValuation.StateRelabelExit

/-!
# Naturality of one actual LinkChain attachment

The true intersection-group maps used by LinkChain commute with the
earlier-stage group isomorphisms. The exact pushout then carries the
whole edge-reflecting chain state to the next relabelled state; its
target separation condition follows from the source condition.
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

/-- One canonical attachment transports its actual edge-reflecting state.
There is no independently hypothesized target separation condition. -/
noncomputable def extendState
    (R : RelabelData D D' S T old old' L L' p)
    (i j : Proper S)
    (C : ChainValuation.ChainState E (block S old i))
    (C' : ChainValuation.ChainState E' (block T old' (R.proper i)))
    (H : ChainValuation.StateRelabel p (R.stage i) C C')
    (h : (old i).Carrier)
    (hsep : Disjoint C.entry
      (ChainValuation.exitSet (block S old i) h
        (left D S old L i j))) :
    ChainValuation.StateRelabel p (R.stage j)
      (ChainValuation.extend
        (block S old i) (block S old j) C h
        (left D S old L i j) (right D S old L i j)
        (left_injective D S old L i j)
        (right_injective D S old L i j)
        hsep (shared_edge D S old L i j))
      (ChainValuation.extend
        (block T old' (R.proper i))
        (block T old' (R.proper j)) C' (R.stage i h)
        (left D' T old' L' (R.proper i) (R.proper j))
        (right D' T old' L' (R.proper i) (R.proper j))
        (left_injective D' T old' L' (R.proper i) (R.proper j))
        (right_injective D' T old' L' (R.proper i) (R.proper j))
        ((ChainValuation.StateRelabel.entry_exit_disjoint_iff
          p (block S old i) (block T old' (R.proper i)) C C'
          (R.stage i) H (R.interface i j) h (R.stage i h)
          (left D S old L i j)
          (left D' T old' L' (R.proper i) (R.proper j)) rfl
          (R.leftComm i j)).mp hsep)
        (shared_edge D' T old' L' (R.proper i) (R.proper j))) :=
  ChainValuation.StateRelabel.extension_from_source
    p (block S old i) (block S old j)
    (block T old' (R.proper i)) (block T old' (R.proper j))
    C C' (R.stage i) (R.stage j) H
    (R.interface i j) h (R.stage i h) rfl
    (left D S old L i j) (right D S old L i j)
    (left D' T old' L' (R.proper i) (R.proper j))
    (right D' T old' L' (R.proper i) (R.proper j))
    (R.leftComm i j) (R.rightComm i j)
    (left_injective D S old L i j)
    (right_injective D S old L i j)
    (left_injective D' T old' L' (R.proper i) (R.proper j))
    (right_injective D' T old' L' (R.proper i) (R.proper j))
    hsep
    (shared_edge D S old L i j)
    (shared_edge D' T old' L' (R.proper i) (R.proper j))
    (R.active j) (R.edge j)

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
