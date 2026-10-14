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
    let k : T → S := fun a => ⟨h.toFun a.val, hRange a.val⟩
    have hk (a : T) : (k a).val = e.toFun a := (he a).symm
    refine ⟨{
      toFun := k
      injective := ?_
      rel_iff := ?_
      out_eq := ?_ }, ?_⟩
    · intro a b hab
      apply e.injective
      calc
        e.toFun a = (k a).val := (hk a).symm
        _ = (k b).val := congrArg Subtype.val hab
        _ = e.toFun b := hk b
    · intro n r xs
      change RB.rel r (fun i => (k (xs i)).val) ↔
        (inducedRelations RA T).rel r xs
      have htuple : (fun i => (k (xs i)).val) =
          (fun i => e.toFun (xs i)) := by
        funext i
        exact hk (xs i)
      rw [htuple]
      exact e.rel_iff r xs
    · intro f a
      apply Set.ext
      intro b
      constructor
      · rintro ⟨z, hz, hzb⟩
        change b.val ∈ outB f (h.toFun a.val)
        have hez : e.toFun z ∈ e.toFun '' (inducedUnary outA T f a) :=
          ⟨z, hz, rfl⟩
        rw [e.out_eq f a] at hez
        have hb : (k z).val = b.val := congrArg Subtype.val hzb
        rw [← hk a, ← hk z, hb] at hez
        exact hez
      · intro hb
        have hz : b.val ∈ outB f (e.toFun a) := by
          rw [← hk a]
          exact hb
        rw [← e.out_eq f a] at hz
        obtain ⟨z, hz, hez⟩ := hz
        have heq : k z = b := Subtype.ext ((hk z).trans hez)
        exact ⟨z, hz, heq⟩
    · intro a
      rfl

end GluingEPPA.Sparsening.Tree
