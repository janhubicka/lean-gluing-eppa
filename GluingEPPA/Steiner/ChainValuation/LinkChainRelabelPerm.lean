import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelSpace
import GluingEPPA.Steiner.ChainValuation.TestCoordinateConjugation

/-!
# Actual chain-space equivariance of completed letter actions

A bijection reflecting every genuine labelled edge also conjugates the
completed matching involutions, including fixed points. The resulting
equivariant choices are enough to transfer the entire finite-test word
kernel, with no functorial choice of the space maps.
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

/-- Actual chain test spaces may be relabelled to intertwine every
completed letter permutation, not merely genuine edge relations. -/
theorem chainPerm_matchingRelabel
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) (c : SeparatedChains D N S old L) :
    ∃ F : chainSpace D N S old L c ≃
      chainSpace D' N T old' L' (chainIndexEquiv D D' S T old old' L L' R N c),
      ∀ (e : E) (x : chainSpace D N S old L c),
        F (chainPerm D N S old L c e x) =
          chainPerm D' N T old' L'
            (chainIndexEquiv D D' S T old old' L L' R N c)
            (p e) (F x) := by
  obtain ⟨F, hrel⟩ := chainSpace_matchingRelabel
    D D' S T old old' L L' R N c
  refine ⟨F, ?_⟩
  intro e x
  exact GluingEPPA.Steiner.ChainValuation.matching_perm_conjugate_of_rel_iff F
    ((chainState D N S old L c).state.matching e)
    ((chainState D' N T old' L'
      (chainIndexEquiv D D' S T old old' L L' R N c)).state.matching (p e))
    (hrel e) x

/-- Choose an equivariant bijection of the actual chain test spaces.
Its choice is irrelevant to the word kernel. -/
noncomputable def chainSpaceEquiv
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) (c : SeparatedChains D N S old L) :
    chainSpace D N S old L c ≃
      chainSpace D' N T old' L' (chainIndexEquiv D D' S T old old' L L' R N c) :=
  Classical.choose (chainPerm_matchingRelabel D D' S T old old' L L' R N c)

theorem chainSpaceEquiv_letter
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) (c : SeparatedChains D N S old L)
    (e : E) (x : chainSpace D N S old L c) :
    chainSpaceEquiv D D' S T old old' L L' R N c
      (chainPerm D N S old L c e x) =
    chainPerm D' N T old' L'
      (chainIndexEquiv D D' S T old old' L L' R N c)
      (p e) (chainSpaceEquiv D D' S T old old' L L' R N c x) :=
  Classical.choose_spec
    (chainPerm_matchingRelabel D D' S T old old' L L' R N c) e x

/-- Under the earlier compatible group/Link relabellings, the entire
added finite-test word kernel is invariant on the actual recorded tests. -/
theorem chainTestKernel_iff
    (R : RelabelData D D' S T old old' L L' p)
    (N : Nat) (w v : List E) :
    AugmentedRecord.testValue
      (chainSpace D N S old L) (chainPerm D N S old L) w =
    AugmentedRecord.testValue
      (chainSpace D N S old L) (chainPerm D N S old L) v ↔
    AugmentedRecord.testValue
      (chainSpace D' N T old' L') (chainPerm D' N T old' L') (w.map p) =
    AugmentedRecord.testValue
      (chainSpace D' N T old' L') (chainPerm D' N T old' L') (v.map p) :=
  AugmentedRecord.testValue_kernel_iff_of_equivariant p
    (chainIndexEquiv D D' S T old old' L L' R N)
    (chainPerm D N S old L) (chainPerm D' N T old' L')
    (fun c => chainSpaceEquiv D D' S T old old' L L' R N c)
    (fun c e x => chainSpaceEquiv_letter D D' S T old old' L L' R N c e x)
    w v

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
