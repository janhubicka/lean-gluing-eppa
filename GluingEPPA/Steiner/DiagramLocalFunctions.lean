import GluingEPPA.Steiner.DiagramFreeRealizationTheorem

/-!
# Exact set-valued completions in arbitrary free Steiner realizations

The main-text free-realization lemma is stated in the function
presentation of partial Steiner systems. The generic certificate
proves closed induced embeddings in relational triple notation.
This theorem supplies the exact missing equation for each local
canonical copy, including all new quotient completions.

The argument uses the already proved closedness of the canonical
copy to establish the reverse inclusion.
-/

namespace GluingEPPA.Steiner.EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u w
variable {V E : Type u} {Ω : Type w}
variable (D : EdgeGraph V E) [Finite V] [Fintype E] [DecidableEq E]

/-- The completion of x,y inside one labelled local Steiner system,
as a set of actual points in that local system. -/
def localCompletionSet (L : LabelledSteiner D Ω)
    (u : V) (x y : Ω) : Set {z : Ω // L.present u z} :=
  {z | L.triple u x y z.val}

/-- The canonical local embedding preserves the binary set-valued
Steiner completion function by equality. The reverse implication
rules out any quotient triple creating a new completion in a
canonical copy, not just a second local triple. -/
theorem canonicalPoint_completion_eq (L : LabelledSteiner D Ω)
    (u : V) (g : (family D Finset.univ).Carrier)
    (x y : Ω) (hx : L.present u x) (hy : L.present u y) :
    (fun z : {z : Ω // L.present u z} =>
      canonicalPoint D L u g z.val z.property) ''
        (localCompletionSet D L u x y) =
      {b : realizedPoint D L |
        realizedTriple D L
          (canonicalPoint D L u g x hx)
          (canonicalPoint D L u g y hy) b} := by
  ext b
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨u, g, x, y, z.val, hz, rfl, rfl, rfl⟩
  · intro h
    obtain ⟨z, hz, hb⟩ := realizedTriple_closed D L u g x y hx hy b h
    refine ⟨⟨z, (L.triple_present u x y z hz).2.2⟩, hz, ?_⟩
    exact hb.symm

end GluingEPPA.Steiner.EdgeGraph.RecursiveRecord
