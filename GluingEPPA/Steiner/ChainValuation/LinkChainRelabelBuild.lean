import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelTail

/-!
# Naturality of the actual nonempty separated-chain builder

The preceding lemmas transport the first block, the genuine two-block
attachment, and every subsequent separated attachment. This file packages
those checked calculations for the actual \`LinkChain.buildNonempty\` used
by \`ChainTests.chainState\`.

This is conditional on the old-stage RelabelData. In particular it does not
construct that data from a diagram isomorphism and does not prove full
augmented-family naturality.
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

/-- The genuine nonempty builder preserves and reflects every *named*
edge after relabelling. The arbitrary final shift in a raw test is carried
along as a normal atom coordinate; it does not change the builder's
recursion or its word kernel. -/
theorem buildNonempty_matchingRelabel
    (R : RelabelData D D' S T old old' L L' p)
    (l : List (Atom S old))
    (hne : l ≠ [])
    (hsep : separatedList D S old L l) :
    ∃ F :
      (buildNonempty D S old L l hne hsep).state.Space ≃
      (buildNonempty D' T old' L'
        (l.map (atomEquiv D D' S T old old' L L' R))
        (by cases l with
            | nil => exact False.elim (hne rfl)
            | cons _ _ => simp)
        ((separatedList_relabel D D' S T old old' L L' R l).mp hsep)).state.Space,
      ∀ e u v,
        ((buildNonempty D S old L l hne hsep).state.matching e).Rel u v ↔
        ((buildNonempty D' T old' L'
          (l.map (atomEquiv D D' S T old old' L L' R))
          (by cases l with
              | nil => exact False.elim (hne rfl)
              | cons _ _ => simp)
          ((separatedList_relabel D D' S T old old' L L' R l).mp hsep)).state.matching (p e)).Rel
          (F u) (F v) := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons x rest =>
    cases rest with
    | nil =>
      let H := firstState D D' S T old old' L L' R x.1
      exact ⟨H.space, H.matching⟩
    | cons y tail =>
      let H := pairState D D' S T old old' L L' R x y
      exact buildTail_matchingRelabel D D' S T old old' L L' R tail x y
        (pair D S old L x y)
        (pair D' T old' L'
          ((atomEquiv D D' S T old old' L L' R) x)
          ((atomEquiv D D' S T old old' L L' R) y))
        H hsep

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
