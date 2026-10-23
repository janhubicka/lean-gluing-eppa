import GluingEPPA.Steiner.DiagramMainEPPA

/-!
# The set-valued-function notation for Steiner closure

The manuscript describes a partial Steiner system by a binary
set-valued function F(x,y) of possible third points. The main Lean
theorem uses an ordered ternary triple relation. They are two
presentations of the same structure: the function value is exactly
the set of third points of a triple.

These lemmas verify the equivalence of closure, the equality required
for a function-language embedding, and the equality required for a
function-language automorphism. No EPPA hypothesis is added.
-/

namespace GluingEPPA.Steiner.InitialSites

universe u v
variable {A : Type u} {B : Type v}

/-- The binary set-valued function used in Section 2 of the paper. -/
def completionSet (R : A → A → A → Prop) (x y : A) : Set A :=
  {z | R x y z}

/-- Triple closure is exactly closure under the binary set-valued
function, including the case where a pair has no completion. -/
theorem closed_iff_completionSet (R : A → A → A → Prop) (U : Set A) :
    Closed R U ↔
      ∀ (x y : A), x ∈ U → y ∈ U →
        completionSet R x y ⊆ U := by
  constructor
  · intro h x y hx hy z hz
    exact h x y z hz hx hy
  · intro h x y z ht hx hy
    exact h x y hx hy ht

/-- A partial Steiner system admits at most one third point for each
pair, as required for the set-valued binary function. -/
theorem input_completion_unique (P : Input A) (x y z w : A)
    (hz : z ∈ completionSet P.triple x y)
    (hw : w ∈ completionSet P.triple x y) : z = w :=
  P.unique x y z w hz hw

/-- The input embedding respects the set-valued function *by
equality*, not merely by inclusion. The reverse inclusion uses
closedness of the canonical root image. -/
theorem witness_embedding_function (P : Input A)
    (C : CoherentEPPAWitness P B) (x y : A) :
    C.embedding '' completionSet P.triple x y =
      completionSet C.triple (C.embedding x) (C.embedding y) := by
  ext b
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (C.embedding_triple x y z).mpr hz
  · intro hb
    obtain ⟨z, hz, heq⟩ := C.embedding_closed x y b hb
    exact ⟨z, hz, heq.symm⟩

/-- A chosen coherent extension is also an automorphism of the
binary set-valued-function presentation of the quotient. -/
theorem witness_extension_function (P : Input A)
    (C : CoherentEPPAWitness P B)
    (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (x y : B) :
    (C.extension U W hU hW f) '' completionSet C.triple x y =
      completionSet C.triple
        ((C.extension U W hU hW f) x)
        ((C.extension U W hU hW f) y) := by
  let e := C.extension U W hU hW f
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (C.extension_triple U W hU hW f x y w).mpr hw
  · intro hz
    refine ⟨e.symm z, ?_, ?_⟩
    · apply (C.extension_triple U W hU hW f x y (e.symm z)).mp
      change C.triple (e x) (e y) z at hz
      simpa only [e.apply_symm_apply] using hz
    · exact e.apply_symm_apply z

end GluingEPPA.Steiner.InitialSites
