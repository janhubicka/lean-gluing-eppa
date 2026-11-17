import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelTail

/-!
# Naturality of every actual finite separated-chain construction

The nonempty builder has three clauses: impossible empty list, the first
one-block Cayley state, and the PairResult followed by the genuine finite
tail recursion. The previously checked chain-state induction provides an
equivalence of every completed quotient, with two-way reflection of the
actual labelled matching edges.
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

private theorem map_nonempty {α β : Type u} (f : α → β)
    {xs : List α} (h : xs ≠ []) : xs.map f ≠ [] := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons x xs => simp

/-- Every literal nonempty separated chain has an edge-reflecting
relabelled space equivalence: no quotient or chain is replaced by a
hypothetical isomorphic test. -/
theorem buildNonempty_matchingRelabel
    (R : RelabelData D D' S T old old' L L' p)
    (atoms : List (Atom S old)) (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    ∃ F :
      (buildNonempty D S old L atoms hne hsep).state.Space ≃
      (buildNonempty D' T old' L'
        (atoms.map (atomEquiv D D' S T old old' L L' R))
        (map_nonempty (atomEquiv D D' S T old old' L L' R) hne)
        ((separatedList_relabel D D' S T old old' L L' R atoms).mp hsep)).state.Space,
      ∀ e u v,
        ((buildNonempty D S old L atoms hne hsep).state.matching e).Rel u v ↔
        ((buildNonempty D' T old' L'
          (atoms.map (atomEquiv D D' S T old old' L L' R))
          (map_nonempty (atomEquiv D D' S T old old' L L' R) hne)
          ((separatedList_relabel D D' S T old old' L L' R atoms).mp hsep)).state.matching
            (p e)).Rel (F u) (F v) := by
  cases atoms with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          have H := firstState D D' S T old old' L L' R x.1
          exact ⟨H.space, H.matching⟩
      | cons y ys =>
          have H := pairState D D' S T old old' L L' R x y
          exact buildTail_matchingRelabel D D' S T old old' L L' R
            ys x y (pair D S old L x y)
            (pair D' T old' L'
              ((atomEquiv D D' S T old old' L L' R) x)
              ((atomEquiv D D' S T old old' L L' R) y))
            H hsep

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
