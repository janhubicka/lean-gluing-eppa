import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelNonempty

/-!
# Naturality of every recorded bounded separated-chain test space

The actual finite test-index equivalence and the literal nonempty builder
are linked: the transported list of raw blocks is exactly its pointwise
relabeling. The full chain builder gives a bijection reflecting every
genuine labelled edge, including when the last shift is unused.
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

/-- A dependent use of buildNonempty respects equality of the underlying
list, including its nonempty and separation proof witnesses. -/
private theorem buildNonempty_congr
    (l m : List (Atom T old')) (h : l = m)
    (hne : l ≠ []) (hme : m ≠ [])
    (hsep : separatedList D' T old' L' l)
    (hsep' : separatedList D' T old' L' m) :
    buildNonempty D' T old' L' l hne hsep =
      buildNonempty D' T old' L' m hme hsep' := by
  cases h
  rfl

/-- The existing finite test space and its actual relabelled counterpart
have an edge-reflecting equivalence. -/
theorem chainSpace_matchingRelabel
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) (c : SeparatedChains D N S old L) :
    ∃ F : chainSpace D N S old L c ≃
      chainSpace D' N T old' L' (chainIndexEquiv D D' S T old old' L L' R N c),
      ∀ (e : E) (u v : chainSpace D N S old L c),
        ((chainState D N S old L c).state.matching e).Rel u v ↔
        ((chainState D' N T old' L'
          (chainIndexEquiv D D' S T old old' L L' R N c)).state.matching (p e)).Rel
            (F u) (F v) := by
  let φ : Atom S old ≃ Atom T old' :=
    atomEquiv D D' S T old old' L L' R
  let atoms : List (Atom S old) := List.ofFn c.1.2
  have hne : atoms ≠ [] := rawChain_list_nonempty N S old c.1
  have hsep : separatedList D S old L atoms := c.2
  have hne' : atoms.map φ ≠ [] := by
    intro h
    exact hne (by
      cases ha : atoms with
      | nil => rfl
      | cons x xs => simp [ha] at h)
  have hsep' : separatedList D' T old' L' (atoms.map φ) :=
    (separatedList_relabel D D' S T old old' L L' R atoms).mp hsep
  obtain ⟨F, hF⟩ := buildNonempty_matchingRelabel
    D D' S T old old' L L' R atoms hne hsep
  have hAtoms :
      List.ofFn ((chainIndexEquiv D D' S T old old' L L' R N c).1.2) =
        atoms.map φ := by
    exact rawRelabel_list D D' S T old old' L L' R N c.1
  have hState :
      chainState D' N T old' L'
        (chainIndexEquiv D D' S T old old' L L' R N c) =
      buildNonempty D' T old' L' (atoms.map φ) hne' hsep' := by
    change buildNonempty D' T old' L'
       (List.ofFn ((chainIndexEquiv D D' S T old old' L L' R N c).1.2)) _ _ =
       buildNonempty D' T old' L' (atoms.map φ) _ _
    exact buildNonempty_congr D' T old' L' _ _ hAtoms _ _ _ _
  have transport : ∀ Q : SomeState T old',
      Q = buildNonempty D' T old' L' (atoms.map φ) hne' hsep' →
      ∃ G : chainSpace D N S old L c ≃ Q.state.Space,
        ∀ (e : E) (u v : chainSpace D N S old L c),
          ((chainState D N S old L c).state.matching e).Rel u v ↔
            (Q.state.matching (p e)).Rel (G u) (G v) := by
    intro Q hQ
    cases hQ
    exact ⟨F, hF⟩
  exact transport _ hState

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
