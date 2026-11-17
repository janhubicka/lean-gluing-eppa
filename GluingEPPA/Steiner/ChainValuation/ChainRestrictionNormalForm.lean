import GluingEPPA.Steiner.ChainValuation.ComponentTraceDichotomy
import GluingEPPA.Steiner.ChainValuation.NormalizedTraceSeparatedTest
import GluingEPPA.Steiner.ChainValuation.NamedHistoryOriginalCorrespondence
import GluingEPPA.Steiner.ChainValuation.ReachComponentTestWords

/-!
# Restriction of an actual bounded separated chain

The finite component-chart induction retains an exact normalized source
trace and its block-count bound. The full/proper dichotomy is made on
that same trace. A proper trace is realized as an actual smaller-stage
separated-chain test; a full trace block gives the actual earlier K_M
Cayley group. Both alternatives preserve and reflect genuine M-edges.

This closes the geometric chain-restriction statement, including its
completed letter actions. It does not construct the simultaneous
augmented recursive family or assume that arbitrary old records already
contain the smaller-chain test coordinates.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E X : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- The two genuine normal forms, with an explicit source block bound
and exact labelled edges on the entire target component. -/
def ComponentNormalForm (M : Proper S) (N bound : Nat)
    (P : E → Matching X) (q : X) : Prop :=
  (∃ F : (old M).Carrier ≃ MatchingReachComponent P M.val q,
    ∀ e ∈ M.val, ∀ x z : (old M).Carrier,
      ((block S old M).matching e).Rel x z ↔
        (P e).Rel (F x).val (F z).val) ∨
  (∃ c : SeparatedChains D N M.val (smallerOld S old M) (smallerLinks D S old L M),
    (c.val.1.val : Nat) ≤ bound ∧
    ∃ F : chainSpace D N M.val (smallerOld S old M) (smallerLinks D S old L M) c ≃
        MatchingReachComponent P M.val q,
      ∀ e ∈ M.val, ∀ x z,
        ((chainState D N M.val (smallerOld S old M) (smallerLinks D S old L M) c).state.matching e).Rel
          x z ↔ (P e).Rel (F x).val (F z).val)

theorem ComponentNormalForm.mono
    {M : Proper S} {N a b : Nat} {P : E → Matching X} {q : X}
    (h : ComponentNormalForm D S old L M N a P q) (hab : a ≤ b) :
    ComponentNormalForm D S old L M N b P q := by
  rcases h with h | ⟨c, hc, F, hF⟩
  · exact Or.inl h
  · exact Or.inr ⟨c, hc.trans hab, F, hF⟩

/-- The same concrete component chart yields one of the two literal
source models, retaining its exact trace-length bound. -/
theorem ComponentChart.normalForm
    {M : Proper S} {R : BuildResult D S old L} {q : R.state.Space}
    (C : ComponentChart D S old L M R q)
    (N : Nat) (hbound : C.trace.length ≤ N) :
    ComponentNormalForm D S old L M N C.trace.length R.state.matching q := by
  rcases C.full_or_proper D S old L with hfull | hproper
  · exact Or.inl hfull
  · let c := C.trace.toSeparatedTest hproper N hbound
    let T := C.trace.testEquiv hproper N hbound
    let F := T.symm.trans C.equiv
    refine Or.inr ⟨c, ?_, F, ?_⟩
    · exact (C.trace.toSeparatedTest_length hproper N hbound).le
    · intro e he x z
      have hsmall := C.trace.testEquiv_edge_iff hproper N hbound e (T.symm x) (T.symm z)
      have hsmall' :
          (C.source.matching e).Rel (T.symm x) (T.symm z) ↔
          ((chainState D N M.val (smallerOld S old M) (smallerLinks D S old L M) c).state.matching e).Rel
            x z := by
        simpa only [T, Equiv.apply_symm_apply] using hsmall
      exact hsmall'.symm.trans (C.edge_iff e he (T.symm x) (T.symm z))

/-- The finite chart induction uses the literal original chain state,
including the dependent current atom, after forgetting its history. -/
theorem coveredBuildNonempty_original_state
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ []) (hsep : separatedList D S old L atoms) :
    let H := coveredNamedAlignedBuildNonempty D S old L M atoms hne hsep
    (⟨H.named.data.chain.current, H.named.data.chain.state⟩ : SomeState S old) =
      buildNonempty D S old L atoms hne hsep := by
  intro H
  change
    (⟨(coveredNamedAlignedBuildNonempty D S old L M atoms hne hsep).named.data.chain.current,
      (coveredNamedAlignedBuildNonempty D S old L M atoms hne hsep).named.data.chain.state⟩ : SomeState S old) = _
  rw [coveredNamedAlignedBuildNonempty_named_eq D S old L M atoms hne hsep]
  exact namedHistoryBuildNonempty_original D S old L M atoms hne hsep

/-- Restriction of a literal bounded separated-chain test to M is
either the actual earlier Cayley graph K_M or a literal earlier
separated-chain test, with no increase in the original block count. -/
theorem chain_restriction
    (N : Nat) (M : Proper S) (c : SeparatedChains D N S old L)
    (q : chainSpace D N S old L c) :
    ComponentNormalForm D S old L M N (c.val.1.val : Nat)
      (chainState D N S old L c).state.matching q := by
  let atoms := List.ofFn c.val.2
  let hne := rawChain_list_nonempty N S old c.val
  let hsep : separatedList D S old L atoms := c.property
  let H := coveredNamedAlignedBuildNonempty D S old L M atoms hne hsep
  let R := H.named.data.chain
  have hcharts := coveredBuildNonempty_componentsCharted D S old L M atoms hne hsep
  have hlen : atoms.length = (c.val.1.val : Nat) := by
    exact List.length_ofFn
  have hN : atoms.length ≤ N := by
    rw [hlen]
    exact Nat.le_of_lt_succ c.val.1.val.isLt
  let P : SomeState S old → Prop := fun T =>
    ∀ x : T.state.Space, ComponentNormalForm D S old L M N (c.val.1.val : Nat)
      T.state.matching x
  have hR : P ⟨R.current, R.state⟩ := by
    intro x
    obtain ⟨C, hC⟩ := hcharts.1 x
    have hmodel := C.normalForm D S old L N (hC.trans hN)
    exact hmodel.mono D S old L (hC.trans hlen.le)
  have hstate : (⟨R.current, R.state⟩ : SomeState S old) = chainState D N S old L c :=
    coveredBuildNonempty_original_state D S old L M atoms hne hsep
  have hactual : P (chainState D N S old L c) := hstate ▸ hR
  exact hactual q

/-- The normal-form equivalences intertwine the completed M-letter
actions, including every fixed point of the partial-matching completion. -/
theorem chain_restriction_completed_actions
    (N : Nat) (M : Proper S) (c : SeparatedChains D N S old L)
    (q : chainSpace D N S old L c) :
    (∃ F : (old M).Carrier ≃
        MatchingReachComponent (chainState D N S old L c).state.matching M.val q,
      ∀ e ∈ M.val, ∀ x : (old M).Carrier,
        (F (((block S old M).matching e).perm x)).val =
          chainPerm D N S old L c e (F x).val) ∨
    (∃ d : SeparatedChains D N M.val (smallerOld S old M) (smallerLinks D S old L M),
      (d.val.1.val : Nat) ≤ (c.val.1.val : Nat) ∧
      ∃ F : chainSpace D N M.val (smallerOld S old M) (smallerLinks D S old L M) d ≃
          MatchingReachComponent (chainState D N S old L c).state.matching M.val q,
        ∀ e ∈ M.val, ∀ x,
          (F (chainPerm D N M.val (smallerOld S old M) (smallerLinks D S old L M) d e x)).val =
            chainPerm D N S old L c e (F x).val) := by
  rcases chain_restriction D S old L N M c q with ⟨F, hF⟩ | ⟨d, hd, F, hF⟩
  · refine Or.inl ⟨F, ?_⟩
    exact componentChart_perm_val_of_edge_iff
      (chainState D N S old L c).state.matching M.val q
      (fun e => (block S old M).matching e) F hF
  · refine Or.inr ⟨d, hd, F, ?_⟩
    exact componentChart_perm_val_of_edge_iff
      (chainState D N S old L c).state.matching M.val q
      (chainState D N M.val (smallerOld S old M) (smallerLinks D S old L M) d).state.matching F hF

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
