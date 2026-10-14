import GluingEPPA.Sparsening.TreeHomEmbeddingTreeGlue

/-!
# Closed-substructure restrictions of homomorphism-embeddings

A homomorphism-embedding is locally exact on irreducible closed tests.
An exact embedding induces a homomorphism-embedding, and every closed
induced substructure has an exact inclusion into its ambient structure.
These two reusable facts show that restriction of a homomorphism-embedding
to a closed test is again a homomorphism-embedding, with no global
injectivity hypothesis.

The constructions preserve all relations (including nullary) and
the equality of entire set-valued unary fibres.
-/

namespace GluingEPPA.Sparsening.Tree

universe u v w t
variable {L : Nat → Type u} {F : Type t}
variable {A : Type v} {B : Type w}

/-- A closed induced unary relational substructure includes exactly
into its ambient structure, including all function fibres. -/
def ExactUnaryEmbedding.closedSubtype
    (RA : RelStructure L A) (outA : F → A → Set A)
    (S : Set A) (hclosed : UnaryClosed outA (fun a => a ∈ S)) :
    ExactUnaryEmbedding (inducedRelations RA S) (inducedUnary outA S)
      RA outA where
  toFun := Subtype.val
  injective := Subtype.val_injective
  rel_iff := by
    intro n r xs
    exact Iff.rfl
  out_eq := by
    intro f x
    exact inducedUnary_full outA S hclosed f x

/-- Forget global exactness to obtain an honest homomorphism-embedding.
On each closed irreducible test the restriction remains an EXACT embedding,
not just a forward homomorphism. -/
def ExactUnaryEmbedding.toHomEmbedding
    {RA : RelStructure L A} {RB : RelStructure L B}
    {outA : F → A → Set A} {outB : F → B → Set B}
    (e : ExactUnaryEmbedding RA outA RB outB) :
    UnaryHomEmbedding RA outA RB outB where
  toFun := e.toFun
  rel_map := by
    intro n r xs hr
    exact (e.rel_iff r xs).mpr hr
  unary_map := by
    intro f a b hb
    have himage : e.toFun b ∈ e.toFun '' outA f a :=
      ⟨b, hb, rfl⟩
    rw [e.out_eq f a] at himage
    exact himage
  exact_on_irred := by
    intro S hclosed hirr
    refine ⟨{
      toFun := fun a => e.toFun a.val
      injective := by
        intro a b hab
        exact Subtype.ext (e.injective hab)
      rel_iff := by
        intro n r xs
        exact e.rel_iff r (fun i => (xs i).val)
      out_eq := by
        intro f x
        calc
          (fun a : S => e.toFun a.val) '' inducedUnary outA S f x =
            e.toFun '' outA f x.val := by
              ext b
              constructor
              · rintro ⟨a, ha, rfl⟩
                exact ⟨a.val, ha, rfl⟩
              · rintro ⟨a, ha, rfl⟩
                exact ⟨⟨a, hclosed f x.val a x.property ha⟩, ha, rfl⟩
          _ = outB f (e.toFun x.val) := e.out_eq f x.val
      }, ?_⟩
    intro z
    rfl

/-- Restriction to any closed induced source remains a homomorphism-embedding.
This transports the actual atlas quotient projection to arbitrary finite
closed test pieces, without asserting injectivity of the whole projection. -/
def UnaryHomEmbedding.restrictClosed
    {RA : RelStructure L A} {RB : RelStructure L B}
    {outA : F → A → Set A} {outB : F → B → Set B}
    (h : UnaryHomEmbedding RA outA RB outB)
    (S : Set A) (hclosed : UnaryClosed outA (fun a => a ∈ S)) :
    UnaryHomEmbedding (inducedRelations RA S) (inducedUnary outA S)
      RB outB :=
  h.comp ((ExactUnaryEmbedding.closedSubtype RA outA S hclosed).toHomEmbedding)

end GluingEPPA.Sparsening.Tree
