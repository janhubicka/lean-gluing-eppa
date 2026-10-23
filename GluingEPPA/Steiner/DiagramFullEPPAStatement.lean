import GluingEPPA.Steiner.DiagramFunctionBridge

/-!
# The main coherent Steiner EPPA theorem in function notation

This final statement eliminates implementation-dependent finiteness
instances on the edge type. Its only hypotheses are a finite input
partial Steiner triple system and a chosen linear order (used to
complete partial bijections coherently).

The returned witness includes a finite partial Steiner system, a
closed induced embedding, and a family of automorphisms extending all
closed partial automorphisms with exact identity and composition.
The further equalities below certify that both the embedding and
extensions preserve the paper's binary set-valued completion function
by equality, not merely by inclusion. No appendix or external theorem
is used.
-/

namespace GluingEPPA.Steiner.InitialSites

universe u
variable {A : Type u} [Fintype A] [LinearOrder A] [DecidableEq A]

/-- The full main theorem for finite partial Steiner triple systems
with closed embeddings, including their binary set-valued functions.
All auxiliary finiteness instances come from finiteness of A. -/
theorem coherentSteinerEPPA_function (P : Input A) :
    ∃ (B : Type u) (C : CoherentEPPAWitness P B),
      (∀ x y : A,
        C.embedding '' completionSet P.triple x y =
          completionSet C.triple (C.embedding x) (C.embedding y)) ∧
      (∀ (U W : Finset A)
        (hU : Closed P.triple (U : Set A))
        (hW : Closed P.triple (W : Set A))
        (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
        (p q : B),
        (C.extension U W hU hW f) '' completionSet C.triple p q =
          completionSet C.triple
            ((C.extension U W hU hW f) p)
            ((C.extension U W hU hW f) q)) := by
  classical
  letI : Fintype (Edge P.triple) := Fintype.ofFinite _
  letI : DecidableEq (Edge P.triple) := Classical.decEq _
  let C := concreteCoherentEPPAWitness P
  refine ⟨_, C, ?_, ?_⟩
  · intro x y
    exact witness_embedding_function P C x y
  · intro U W hU hW f p q
    exact witness_extension_function P C U W hU hW f p q

end GluingEPPA.Steiner.InitialSites
