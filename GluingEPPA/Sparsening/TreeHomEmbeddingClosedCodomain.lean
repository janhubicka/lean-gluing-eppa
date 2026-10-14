import GluingEPPA.Sparsening.TreeHomEmbeddingRestrict

/-!
# Corestrict a homomorphism-embedding to a closed target image

For a closed old image S containing the range of a homomorphism-embedding,
regard the same map as taking values in the structure induced on S.
This is again a homomorphism-embedding: on any closed irreducible
source test, use its exact source-to-ambient-target embedding and factor
it through the exact inclusion of the closed old image S.

This is the precise bridge from a canonical upstairs projection
to the old induced projected side required by the size-only
sparsening induction. No global injection, reflection outside
irreducible tests, or free decomposition of the old image is assumed.
-/

namespace GluingEPPA.Sparsening.Tree

universe u v w t
variable {L : Nat → Type u} {F : Type t}
variable {A : Type v} {B : Type w}

/-- Restrict the CODOMAIN to any closed induced old set containing the
whole range of the map. Exactness on irreducibles is preserved, including
all full set-valued unary fibres and nullary relation symbols. -/
noncomputable def UnaryHomEmbedding.intoClosedCodomain
    {RA : RelStructure L A} {RB : RelStructure L B}
    {outA : F → A → Set A} {outB : F → B → Set B}
    (h : UnaryHomEmbedding RA outA RB outB)
    (S : Set B)
    (hclosed : UnaryClosed outB (fun b => b ∈ S))
    (hRange : ∀ a : A, h.toFun a ∈ S) :
    UnaryHomEmbedding RA outA
      (inducedRelations RB S) (inducedUnary outB S) where
  toFun := fun a => ⟨h.toFun a, hRange a⟩
  rel_map := by
    intro n r xs hr
    change RB.rel r (fun i => h.toFun (xs i))
    exact h.rel_map r xs hr
  unary_map := by
    intro f a b hb
    change h.toFun b ∈ outB f (h.toFun a)
    exact h.unary_map f a b hb
  exact_on_irred := by
    intro T hT hirr
    obtain ⟨e, he⟩ := h.exact_on_irred T hT hirr
    let block := ExactUnaryEmbedding.closedSubtype RB outB S hclosed
    have hmem : ∀ a : T, ∃ b : S, block.toFun b = e.toFun a := by
      intro a
      refine ⟨⟨h.toFun a.val, hRange a.val⟩, ?_⟩
      exact (he a).symm
    let e' := ExactUnaryEmbedding.factor_through e block hmem
    refine ⟨e', ?_⟩
    intro a
    apply Subtype.ext
    have hfac := ExactUnaryEmbedding.factor_through_spec e block hmem a
    change (e'.toFun a).val = h.toFun a.val
    exact hfac.trans (he a)

end GluingEPPA.Sparsening.Tree
