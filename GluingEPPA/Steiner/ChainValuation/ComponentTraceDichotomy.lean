import GluingEPPA.Steiner.ChainValuation.ComponentChartInduction
import GluingEPPA.Steiner.ChainValuation.NormalizedTraceBlocks
import GluingEPPA.Steiner.ChainValuation.SaturatedMatchingComponent

/-!
# Full-group or proper-mask dichotomy for the actual normalization trace

The finite chart induction chooses its own normalized source trace.
Its proper/full distinction can therefore be made on that same trace,
without identifying its choices with an independent historical interval.

If a trace block contains every letter of M, its embedded image already
has an internal neighbour for every M-letter. Matching uniqueness makes
this image saturated in the target component. Every target point is
connected to the image of the identity, so saturation gives surjectivity.
No separate connectedness theorem for the normalized source is required.
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
variable (L : ∀ m t : Proper S, m.val ⊆ t.val → Link D (old m) (old t))

open GluingEPPA.Steiner.ChainValuation

/-- A full-mask constituent of the concrete source trace gives a
genuine Cayley equivalence onto the entire original component. -/
theorem ComponentChart.fullTraceBlock_equiv
    {M : Proper S} {R : BuildResult D S old L} {q : R.state.Space}
    (C : ComponentChart D S old L M R q)
    (B : Proper S) (hB : B ∈ C.trace.masks) (hfull : M.val ⊆ B.val) :
    ∃ F : (old (Step.meet S M B)).Carrier ≃
        MatchingReachComponent R.state.matching M.val q,
      ∀ e ∈ M.val, ∀ x z : (old (Step.meet S M B)).Carrier,
        ((block S old (Step.meet S M B)).matching e).Rel x z ↔
          (R.state.matching e).Rel (F x).val (F z).val := by
  obtain ⟨f, hf, hEdges⟩ := C.trace.block_embedding D S old L B hB
  let G : (old (Step.meet S M B)).Carrier →
      MatchingReachComponent R.state.matching M.val q := fun x => C.equiv (f x)
  have hG : Function.Injective G := C.equiv.injective.comp hf
  have hGEdge : ∀ e ∈ M.val, ∀ x : (old (Step.meet S M B)).Carrier,
      (R.state.matching e).Rel (G x).val
        (G (x * (old (Step.meet S M B)).edge e)).val := by
    intro e he x
    exact (C.edge_iff e he _ _).mp
      (hEdges e (Finset.mem_inter.mpr ⟨he, hfull he⟩) x)
  have hsat : MatchingSaturated R.state.matching M.val
      (Set.range (fun x => (G x).val)) := by
    intro e he x hx
    obtain ⟨t, rfl⟩ := hx
    exact ⟨(G (t * (old (Step.meet S M B)).edge e)).val,
      ⟨t * (old (Step.meet S M B)).edge e, rfl⟩, hGEdge e he t⟩
  have hGSurj : Function.Surjective G := by
    intro v
    let t : (old (Step.meet S M B)).Carrier := 1
    have hPath : LabelReach (fun e => (R.state.matching e).Rel) M.val
        (G t).val v.val :=
      LabelReach.trans (LabelReach.symm (G t).property) v.property
    have hv : v.val ∈ Set.range (fun x => (G x).val) :=
      (MatchingSaturated.reach_mem_iff R.state.matching M.val
        (Set.range (fun x => (G x).val)) hsat hPath).mp ⟨t, rfl⟩
    obtain ⟨x, hx⟩ := hv
    exact ⟨x, Subtype.ext hx⟩
  let F : (old (Step.meet S M B)).Carrier ≃
      MatchingReachComponent R.state.matching M.val q :=
    Equiv.ofBijective G ⟨hG, hGSurj⟩
  refine ⟨F, ?_⟩
  intro e he x z
  constructor
  · rintro ⟨_, rfl⟩
    exact hGEdge e he x
  · intro h
    have hz : (G z).val = (G (x * (old (Step.meet S M B)).edge e)).val :=
      (R.state.matching e).unique h (hGEdge e he x)
    have hcoord : z = x * (old (Step.meet S M B)).edge e :=
      hG (Subtype.ext hz)
    exact ⟨Finset.mem_inter.mpr ⟨he, hfull he⟩, hcoord⟩

/-- The same trace either contains a full K_M component or all of its
source masks give genuine proper earlier indices below M. -/
theorem ComponentChart.full_or_proper
    {M : Proper S} {R : BuildResult D S old L} {q : R.state.Space}
    (C : ComponentChart D S old L M R q) :
    (∃ F : (old M).Carrier ≃ MatchingReachComponent R.state.matching M.val q,
      ∀ e ∈ M.val, ∀ x z : (old M).Carrier,
        ((block S old M).matching e).Rel x z ↔
          (R.state.matching e).Rel (F x).val (F z).val) ∨
      (∀ B ∈ C.trace.masks, ¬ M.val ⊆ B.val) := by
  by_cases hfull : ∃ B ∈ C.trace.masks, M.val ⊆ B.val
  · obtain ⟨B, hB, hMB⟩ := hfull
    have hindex : Step.meet S M B = M := by
      apply Subtype.ext
      exact Finset.inter_eq_left.mpr hMB
    left
    have h := C.fullTraceBlock_equiv D S old L B hB hMB
    rw [hindex] at h
    exact h
  · right
    intro B hB hMB
    exact hfull ⟨B, hB, hMB⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
