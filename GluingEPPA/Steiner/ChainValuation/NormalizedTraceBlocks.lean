import GluingEPPA.Steiner.ChainValuation.NormalizedChainTrace

/-!
# Genuine block embeddings retained by a normalized construction trace

Every constituent restricted Cayley group embeds in the exact final
source state of the trace, and all its genuine generator edges persist.
This allows the full-mask alternative to be detected directly on the
trace, without identifying its choices with a separate historical chart.
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

/-- Every mask recorded by the trace names a genuinely embedded
restricted Cayley block in its exact final source state. -/
theorem NormalizedChainTrace.block_embedding
    {M A : Proper S}
    {C : ChainState.{u,u} E (block S old (Step.meet S M A))}
    (T : NormalizedChainTrace D S old L M A C)
    (B : Proper S) (hB : B ∈ T.masks) :
    ∃ f : (old (Step.meet S M B)).Carrier → C.Space,
      Function.Injective f ∧
      ∀ e ∈ (Step.meet S M B).val, ∀ t,
        (C.matching e).Rel (f t) (f (t * (old (Step.meet S M B)).edge e)) := by
  induction T generalizing B with
  | single A =>
      have hBA : B = A := List.mem_singleton.mp hB
      subst B
      refine ⟨id, Function.injective_id, ?_⟩
      intro e he t
      exact (block S old (Step.meet S M A)).matching_rel he t
  | @attach A C previous B' shift hsep hshared ih =>
      change B ∈ previous.masks ++ [B'] at hB
      rcases List.mem_append.mp hB with hOld | hNew
      · obtain ⟨f, hf, hEdges⟩ := ih B hOld
        let F := oldEmbed
          (block S old (Step.meet S M A))
          (block S old (Step.meet S M B')) C shift
          (normalizedCommonLeft D S old L M A B')
          (normalizedCommonRight D S old L M A B')
          (normalizedCommonLeft_injective D S old L M A B')
          (normalizedCommonRight_injective D S old L M A B')
        refine ⟨F ∘ f, ?_, ?_⟩
        · exact (oldEmbed_injective
            (block S old (Step.meet S M A))
            (block S old (Step.meet S M B')) C shift
            (normalizedCommonLeft D S old L M A B')
            (normalizedCommonRight D S old L M A B')
            (normalizedCommonLeft_injective D S old L M A B')
            (normalizedCommonRight_injective D S old L M A B')).comp hf
        · intro e he t
          exact Or.inl ⟨f t, f (t * (old (Step.meet S M B)).edge e),
            hEdges e he t, rfl, rfl⟩
      · have hBB : B = B' := List.mem_singleton.mp hNew
        subst B
        refine ⟨newEmbed
          (block S old (Step.meet S M A))
          (block S old (Step.meet S M B')) C shift
          (normalizedCommonLeft D S old L M A B')
          (normalizedCommonRight D S old L M A B')
          (normalizedCommonLeft_injective D S old L M A B')
          (normalizedCommonRight_injective D S old L M A B'), ?_, ?_⟩
        · exact newEmbed_injective
            (block S old (Step.meet S M A))
            (block S old (Step.meet S M B')) C shift
            (normalizedCommonLeft D S old L M A B')
            (normalizedCommonRight D S old L M A B')
            (normalizedCommonLeft_injective D S old L M A B')
            (normalizedCommonRight_injective D S old L M A B')
        · intro e he t
          exact Or.inr ⟨t, he, rfl, rfl⟩

end LinkChain
end RecursiveRecord
end EdgeGraph
end GluingEPPA.Steiner
