import GluingEPPA.Steiner.ChainValuation.FullMaskHistoricalComponent

/-!
# Finite-chain dichotomy: one full K_M block or all proper submasks

The first alternative in the manuscript's chain-restriction lemma
is stronger than a statement about a component based at a chosen
historical block: the actual component can be rooted at an arbitrary
quotient point q. We transport the exact full-mask component result
along any genuine M-path from q to the historical chart.

Classical case analysis then gives a precise normalized induction
split: either a full K_M coset is the entire component, or EVERY
historical block met by the component has strictly smaller
M-intersection alphabet. The latter is the only case needing
finite-interval normalized chain assembly.

All assertions refer to the original named finite-chain quotient.
No global normalized proper-mask chain is asserted here.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph
namespace RecursiveRecord
namespace LinkChain

attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]
variable (S : Finset E) (old : ∀ i : Proper S, Data E i.val)
variable (L : ∀ m t : Proper S, m.val ⊆ t.val →
  Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- A full-M historical coset is the WHOLE component even if the
component was originally rooted at a vertex q outside that block.
The chosen witness x records the actual path from q to the block. -/
theorem NamedHistoricalBlock.fullMask_component_of_meets
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (hEdges : T.HasGenuineLetterEdges D S old L)
    (hfull : M.val ⊆ T.source.val)
    (q : R.state.Space)
    (base : (old T.source).Carrier)
    (hqx : LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (T.chart.embed base))
    (v : R.state.Space) :
    LabelReach (fun e => (R.state.matching e).Rel) M.val q v ↔
      v ∈ T.restrictedCosetImage D S old L base := by
  have hbase :
      LabelReach (fun e => (R.state.matching e).Rel) M.val q v ↔
      LabelReach (fun e => (R.state.matching e).Rel) M.val
        (T.chart.embed base) v := by
    constructor
    · intro h
      exact LabelReach.trans (LabelReach.symm hqx) h
    · intro h
      exact LabelReach.trans hqx h
  exact hbase.trans
    (T.fullMask_component_iff D S old L hEdges hfull base v)

/-- A named historical K_A block is touched by the actual M-component
of q precisely when at least one of its chart points is reachable. -/
def NamedHistoricalBlock.Meets
    {M : Proper S} {R : BuildResult D S old L}
    (T : NamedHistoricalBlock D S old L M R)
    (q : R.state.Space) : Prop :=
  ∃ x : (old T.source).Carrier,
    LabelReach (fun e => (R.state.matching e).Rel) M.val
      q (T.chart.embed x)

/-- For a full-M source mask, every component touching that
historical block is exactly its own selected K_M coset. -/
theorem namedHistoryBuildNonempty_fullMask_meets
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms)
    (T : NamedHistoricalBlock D S old L M
      (namedHistoryBuildNonempty D S old L M atoms hne hsep).data.chain)
    (hT : T ∈ (namedHistoryBuildNonempty
      D S old L M atoms hne hsep).named)
    (hfull : M.val ⊆ T.source.val)
    (q : (namedHistoryBuildNonempty
      D S old L M atoms hne hsep).data.chain.state.Space)
    (hMeets : T.Meets D S old L q) :
    ∃ base : (old T.source).Carrier,
      ∀ v : (namedHistoryBuildNonempty
        D S old L M atoms hne hsep).data.chain.state.Space,
        LabelReach
          (fun e => ((namedHistoryBuildNonempty
            D S old L M atoms hne hsep).data.chain.state.matching e).Rel)
          M.val q v ↔ v ∈ T.restrictedCosetImage D S old L base := by
  obtain ⟨base, hReach⟩ := hMeets
  refine ⟨base, ?_⟩
  intro v
  exact T.fullMask_component_of_meets D S old L
    (namedHistoryBuildNonempty_allGenuineLetterEdges
      D S old L M atoms hne hsep T hT)
    hfull q base hReach v

/-- The FINITE original chain admits the exact required split:
either some full-M historical block captures an entire component,
or every historical block which the component touches has an
alphabet strictly smaller than M after intersection.

This theorem does not choose normalized shifts or identify a
proper-mask interval with a smaller chain. Those remain pending. -/
theorem namedHistoryBuildNonempty_full_or_proper
    (M : Proper S) (atoms : List (Atom S old))
    (hne : atoms ≠ [])
    (hsep : separatedList D S old L atoms) :
    let H := namedHistoryBuildNonempty D S old L M atoms hne hsep
    ∀ q : H.data.chain.state.Space,
      (∃ T : NamedHistoricalBlock D S old L M H.data.chain,
        T ∈ H.named ∧ M.val ⊆ T.source.val ∧ T.Meets D S old L q ∧
        ∃ base : (old T.source).Carrier,
          ∀ v : H.data.chain.state.Space,
            LabelReach (fun e => (H.data.chain.state.matching e).Rel)
              M.val q v ↔
              v ∈ T.restrictedCosetImage D S old L base) ∨
      (∀ T : NamedHistoricalBlock D S old L M H.data.chain,
        T ∈ H.named → T.Meets D S old L q →
        (M.val ∩ T.source.val) ≠ M.val) := by
  intro H q
  classical
  by_cases hFull : ∃ T : NamedHistoricalBlock D S old L M H.data.chain,
      T ∈ H.named ∧ M.val ⊆ T.source.val ∧ T.Meets D S old L q
  · left
    obtain ⟨T, hT, hmask, hMeets⟩ := hFull
    refine ⟨T, hT, hmask, hMeets, ?_⟩
    exact namedHistoryBuildNonempty_fullMask_meets
      D S old L M atoms hne hsep T hT hmask q hMeets
  · right
    intro T hT hMeets heq
    apply hFull
    have hsubset : M.val ⊆ T.source.val := by
      intro e he
      have hm : e ∈ M.val ∩ T.source.val := by
        rw [heq]
        exact he
      exact (Finset.mem_inter.mp hm).2
    exact ⟨T, hT, hsubset, hMeets⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
