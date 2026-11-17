import GluingEPPA.Steiner.ChainValuation.LinkChainRelabelPair

/-!
# Naturality of the next actual finite-chain block

Any pair-stage equivalence transports across one more separated
attachment. The separation hypothesis used by the literal builder
is exactly disjointness of its recorded entry and next exit coset.
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

/-- The builder's triple separation is exactly entry/exit disjointness
of the recorded PairResult and its next actual block. -/
theorem pair_next_exit_disjoint
    (x y z : Atom S old)
    (P : PairResult D S old L x y)
    (hsep : tripleSeparated D S old L x y z) :
    Disjoint P.state.entry
      (ChainValuation.exitSet (block S old y.1) y.2
        (left D S old L y.1 z.1)) := by
  have hentry :
      Set.range (right D S old L x.1 y.1) =
        ChainValuation.leftCoset (right D S old L x.1 y.1).range 1 :=
    ChainValuation.range_eq_leftCoset_one _
  have hexit :
      ChainValuation.exitSet (block S old y.1) y.2
        (left D S old L y.1 z.1) =
        ChainValuation.leftCoset (left D S old L y.1 z.1).range y.2 :=
    ChainValuation.translated_range_eq_leftCoset
      (left D S old L y.1 z.1) y.2
  rw [P.entry_spec, hentry, hexit]
  exact hsep

/-- One genuine PairResult extension is natural, using the original
finite builder on both sides rather than a replacement construction. -/
noncomputable def nextState
    (R : RelabelData D D' S T old old' L L' p)
    (x y : Atom S old)
    (P : PairResult D S old L x y)
    (P' : PairResult D' T old' L'
      ((atomEquiv D D' S T old old' L L' R) x)
      ((atomEquiv D D' S T old old' L L' R) y))
    (H : ChainValuation.StateRelabel p (R.stage y.1) P.state P'.state)
    (z : Atom S old)
    (hsep : tripleSeparated D S old L x y z) :
    ChainValuation.StateRelabel p (R.stage z.1)
      (next D S old L P z hsep).state
      (next D' T old' L' P'
        ((atomEquiv D D' S T old old' L L' R) z)
        ((tripleSeparated_iff D D' S T old old' L L' R x y z).mp hsep)).state := by
  have hd := pair_next_exit_disjoint D S old L x y z P hsep
  exact extendState D D' S T old old' L L' R y.1 z.1
    P.state P'.state H y.2 hd

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord.LinkChain.RelabelData
