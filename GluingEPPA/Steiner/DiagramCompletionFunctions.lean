import GluingEPPA.Steiner.DiagramMainEPPA

/-!
# Set-valued Steiner functions for the main coherent EPPA theorem

A partial Steiner triple system is presented in the manuscript by its
binary set-valued completion function. Its value on (x,y) is the set
of third points of triples containing x,y. The theorems below bridge
the ordered-triple Lean representation of the witness to *exact*
equality of the corresponding function values.

In particular a closed root embedding gives equality (not just
inclusion) of the function values under image, and each selected
extension preserves the set-valued function globally.
-/

namespace GluingEPPA.Steiner.InitialSites

universe u v

/-- The binary set-valued Steiner completion function. -/
def completionSet {X : Type u} (T : X → X → X → Prop)
    (x y : X) : Set X := {z | T x y z}

/-- A closed induced embedding is exactly a homomorphism for the
set-valued completion function: there are no new third points. -/
theorem CoherentEPPAWitness.embedding_completion_eq
    {A : Type u} {B : Type v} {P : Input A}
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

/-- Every coherent extension acts as an automorphism of the *function*
presentation, not merely as a permutation preserving relational
triples in one direction. -/
theorem CoherentEPPAWitness.extension_completion_eq
    {A : Type u} {B : Type v} {P : Input A}
    (C : CoherentEPPAWitness P B)
    (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (p q : B) :
    (C.extension U W hU hW f) '' completionSet C.triple p q =
      completionSet C.triple
        ((C.extension U W hU hW f) p)
        ((C.extension U W hU hW f) q) := by
  ext b
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (C.extension_triple U W hU hW f p q z).mpr hz
  · intro hb
    let e := C.extension U W hU hW f
    have hz : C.triple p q (e.symm b) := by
      apply (C.extension_triple U W hU hW f p q (e.symm b)).mp
      simpa only [e.apply_symm_apply] using hb
    exact ⟨e.symm b, hz, e.apply_symm_apply b⟩

end GluingEPPA.Steiner.InitialSites
