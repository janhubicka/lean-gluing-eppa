import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelPackage
import GluingEPPA.Steiner.ChainValuation.AugmentedStepNaturality

/-!
# The actual augmented successor record preserves word equalities

The previous modules constructed equivalences of the *actual* bounded
separated-chain tests and the injective homomorphisms of their completed
letter-permutation coordinates. Consequently the generic augmented-step
naturality lemma now applies to the literal LinkChain test package.

This theorem takes old-stage RelabelData as its induction hypothesis.
It does not assume a current-stage group isomorphism or an equivariant
finite test package. The remaining strong induction must construct those
old-stage data from an actual diagram isomorphism.
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

/-- All proper target-stage generator isomorphisms are already contained in
the concrete RelabelData, without choosing new arbitrary stage maps. -/
theorem earlierStageIsos
    {p : E ≃ E'}
    (R : RelabelData D D' S T old old' L L' p) :
    ∀ j : Proper T, ∃ i : Proper S,
      ∃ F : (old i).Carrier ≃* (old' j).Carrier,
        (∀ e, p e ∈ j.val ↔ e ∈ i.val) ∧
        (∀ e ∈ i.val, F ((old i).edge e) = (old' j).edge (p e)) := by
  intro j
  obtain ⟨i, rfl⟩ := R.proper.surjective j
  exact ⟨i, R.stage i, fun e => (R.active i e).symm, R.edge i⟩

/-- Full augmented word equality is preserved through an ACTUAL bounded
separated-chain stage, using the constructed test-index maps, not an
equivariant-completion assumption. -/
theorem actualAugmentedStep_preserves_word_equalities
    (f : Iso D D')
    (hST : ∀ e, f.edge e ∈ T ↔ e ∈ S)
    (R : RelabelData D D' S T old old' L L' f.edge)
    (N : Nat) (w v : List E)
    (hw : ∀ e ∈ w, e ∈ S) (hv : ∀ e ∈ v, e ∈ S)
    (hvalue :
      (w.map (AugmentedStep.data D S old
        (chainSpace D N S old L)
        (chainPerm D N S old L)
        (chainPerm_square D N S old L)).edge).prod =
      (v.map (AugmentedStep.data D S old
        (chainSpace D N S old L)
        (chainPerm D N S old L)
        (chainPerm_square D N S old L)).edge).prod) :
    (w.map (fun e => (AugmentedStep.data D' T old'
      (chainSpace D' N T old' L')
      (chainPerm D' N T old' L')
      (chainPerm_square D' N T old' L')).edge (f.edge e))).prod =
    (v.map (fun e => (AugmentedStep.data D' T old'
      (chainSpace D' N T old' L')
      (chainPerm D' N T old' L')
      (chainPerm_square D' N T old' L')).edge (f.edge e))).prod := by
  obtain ⟨q, F, hF, hInj⟩ :=
    concreteTestCoordinates D D' S T old old' L L' R N
  exact AugmentedStep.preserves_word_equalities
    D S old (chainSpace D N S old L)
    (chainPerm D N S old L) (chainPerm_square D N S old L)
    D' f T old' hST (earlierStageIsos D D' S T old old' L L' R)
    (chainSpace D' N T old' L')
    (chainPerm D' N T old' L') (chainPerm_square D' N T old' L')
    q F hF hInj w v hw hv hvalue

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
