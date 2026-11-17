import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelNext
import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelIndex

/-!
# Naturality of the literal finite chain-tail recursion

The last block varies with the input list. During the induction we
retain the stronger StateRelabel interface to extend one block;
the conclusion only needs the final space equivalence reflecting
genuine edges. This avoids dependent last-block casts.
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

/-- The original buildTail recursor has an exact edge-reflecting
equivalence of its resulting quotient spaces for any separated list. -/
theorem buildTail_matchingRelabel
    (R : RelabelData D D' S T old old' L L' p) :
    ∀ (rest : List (Atom S old)) (x y : Atom S old)
      (P : PairResult D S old L x y)
      (P' : PairResult D' T old' L'
        ((atomEquiv D D' S T old old' L L' R) x)
        ((atomEquiv D D' S T old old' L L' R) y))
      (H : ChainValuation.StateRelabel p (R.stage y.1) P.state P'.state)
      (hsep : separatedList D S old L (x :: y :: rest)),
      ∃ F :
        (buildTail D S old L x y P rest hsep).state.Space ≃
        (buildTail D' T old' L'
          ((atomEquiv D D' S T old old' L L' R) x)
          ((atomEquiv D D' S T old old' L L' R) y) P'
          (rest.map (atomEquiv D D' S T old old' L L' R))
          ((separatedList_relabel D D' S T old old' L L' R
            (x :: y :: rest)).mp hsep)).state.Space,
        ∀ e u v,
          ((buildTail D S old L x y P rest hsep).state.matching e).Rel u v ↔
          ((buildTail D' T old' L'
            ((atomEquiv D D' S T old old' L L' R) x)
            ((atomEquiv D D' S T old old' L L' R) y) P'
            (rest.map (atomEquiv D D' S T old old' L L' R))
            ((separatedList_relabel D D' S T old old' L L' R
              (x :: y :: rest)).mp hsep)).state.matching (p e)).Rel (F u) (F v) := by
  intro rest
  induction rest with
  | nil =>
      intro x y P P' H hsep
      exact ⟨H.space, H.matching⟩
  | cons z zs ih =>
      intro x y P P' H hsep
      have ht : tripleSeparated D S old L x y z := hsep.1
      have htail : separatedList D S old L (y :: z :: zs) := hsep.2
      let Pnext := next D S old L P z ht
      let Pnext' := next D' T old' L' P'
        ((atomEquiv D D' S T old old' L L' R) z)
        ((tripleSeparated_iff D D' S T old old' L L' R x y z).mp ht)
      have Hnext := nextState D D' S T old old' L L' R
        x y P P' H z ht
      exact ih y z Pnext Pnext' Hnext htail

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
