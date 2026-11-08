import GluingEPPA.Steiner.DiagramRootWitness
import GluingEPPA.Steiner.DiagramUniformExtension

/-!
# Coherent EPPA for closed partial Steiner triple systems

This is the terminal, *main-text* theorem, combining the actual recursive
valuation, its finite free quotient, the closed root embedding, and the
three-factor extension formula. The quotient is not assumed to be a
Steiner system: its distinctness, symmetry, unique third point, and
closed root copy are proved in the imported modules.

The data explicitly include an extension for every isomorphism between
closed induced subsystems, preserving and reflecting triples. Identity
and composition agree exactly for compatible partial maps.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord

attribute [local instance] Classical.propDecidable

universe u v

/-- The full assertion of coherent EPPA for a fixed finite input,
expressed using ordered triples. The witness's closed embedding and
the coherent choice of automorphisms are part of the structure. -/
structure CoherentEPPAWitness {A : Type u} (P : Input A) (B : Type v) where
  finite : Finite B
  triple : B → B → B → Prop
  unique : ∀ p q r s, triple p q r → triple p q s → r = s
  swap : ∀ p q r, triple p q r → triple q p r
  rotate : ∀ p q r, triple p q r → triple q r p
  distinct : ∀ p q r, triple p q r →
    p ≠ q ∧ p ≠ r ∧ q ≠ r
  embedding : A → B
  embedding_injective : Function.Injective embedding
  embedding_triple : ∀ x y z,
    triple (embedding x) (embedding y) (embedding z) ↔ P.triple x y z
  embedding_closed : ∀ x y b,
    triple (embedding x) (embedding y) b →
      ∃ z, P.triple x y z ∧ b = embedding z
  extension :
    ∀ (U W : Finset A) (hU : Closed P.triple (U : Set A))
      (hW : Closed P.triple (W : Set A)),
      ({x : A // x ∈ U} ≃ {x : A // x ∈ W}) → Equiv.Perm B
  extension_triple :
    ∀ (U W : Finset A) (hU : Closed P.triple (U : Set A))
      (hW : Closed P.triple (W : Set A))
      (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
      (p q r : B),
    triple ((extension U W hU hW f) p)
      ((extension U W hU hW f) q)
      ((extension U W hU hW f) r) ↔ triple p q r
  extension_on :
    ∀ (U W : Finset A) (hU : Closed P.triple (U : Set A))
      (hW : Closed P.triple (W : Set A))
      (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W}),
    (∀ (x y z : A) (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U),
      P.triple x y z ↔
        P.triple (f ⟨x, hx⟩).val
          (f ⟨y, hy⟩).val (f ⟨z, hz⟩).val) →
    ∀ (x : A) (hx : x ∈ U),
      (extension U W hU hW f) (embedding x) =
        embedding (f ⟨x, hx⟩).val
  extension_id :
    ∀ (U : Finset A) (hU : Closed P.triple (U : Set A)),
      extension U U hU hU (Equiv.refl {x : A // x ∈ U}) =
        Equiv.refl B
  extension_comp :
    ∀ (U W T : Finset A) (hU : Closed P.triple (U : Set A))
      (hW : Closed P.triple (W : Set A))
      (hT : Closed P.triple (T : Set A))
      (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
      (g : {x : A // x ∈ W} ≃ {x : A // x ∈ T}),
      (extension U W hU hW f).trans (extension W T hW hT g) =
        extension U T hU hT (f.trans g)

variable {A : Type u} [Fintype A] [LinearOrder A] [DecidableEq A]
variable (P : Input A)
variable [Fintype (Edge P.triple)] [DecidableEq (Edge P.triple)]

/-- The three-factor extensions reflect as well as preserve triples.
The reverse implication uses the chosen extension for the inverse
partial bijection; coherence makes it the inverse permutation. -/
theorem coherentExtension_triple_iff
    (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (p q r : realizedPoint (graph P.triple) (localDiagram P)) :
    realizedTriple (graph P.triple) (localDiagram P)
      ((coherentExtension P U W hU hW f) p)
      ((coherentExtension P U W hU hW f) q)
      ((coherentExtension P U W hU hW f) r) ↔
    realizedTriple (graph P.triple) (localDiagram P) p q r := by
  let B := realizedPoint (graph P.triple) (localDiagram P)
  have hcancel :
      (coherentExtension P U W hU hW f).trans
        (coherentExtension P W U hW hU f.symm) =
      Equiv.refl B := by
    rw [coherentExtension_comp]
    have hff : f.trans f.symm = Equiv.refl {x : A // x ∈ U} := by
      apply Equiv.ext
      intro x
      exact f.symm_apply_apply x
    rw [hff]
    exact coherentExtension_id P U hU
  have hback (x : B) :
      (coherentExtension P W U hW hU f.symm)
        ((coherentExtension P U W hU hW f) x) = x := by
    have hx := congrArg (fun k : Equiv.Perm B => k x) hcancel
    simpa only [Equiv.trans_apply, Equiv.refl_apply] using hx
  constructor
  · intro h
    have h' := coherentExtension_preserves_triple P W U hW hU f.symm
      ((coherentExtension P U W hU hW f) p)
      ((coherentExtension P U W hU hW f) q)
      ((coherentExtension P U W hU hW f) r) h
    simpa only [hback] using h'
  · intro h
    exact coherentExtension_preserves_triple P U W hU hW f p q r h

/-- The actual finite recursive-gluing quotient is a coherent
EPPA witness for every finite partial Steiner triple system, with
embeddings and partial maps taken on closed induced substructures.
All clauses refer to this one concrete quotient and its maps. -/
noncomputable def concreteCoherentEPPAWitness :
    CoherentEPPAWitness P
      (realizedPoint (graph P.triple) (localDiagram P)) where
  finite := rootWitness_finite P
  triple := realizedTriple (graph P.triple) (localDiagram P)
  unique := by
    intro p q r s hr hs
    exact realizedTriple_unique (graph P.triple) (localDiagram P)
      p q r s hr hs
  swap := by
    intro p q r h
    exact realizedTriple_swap (graph P.triple) (localDiagram P) p q r h
  rotate := by
    intro p q r h
    exact realizedTriple_rotate (graph P.triple) (localDiagram P) p q r h
  distinct := by
    intro p q r h
    exact realizedTriple_distinct (graph P.triple) (localDiagram P) p q r h
  embedding := rootEmbedding P
  embedding_injective := rootEmbedding_injective P
  embedding_triple := by
    intro x y z
    exact rootEmbedding_triple_iff P x y z
  embedding_closed := by
    intro x y b h
    exact rootEmbedding_closed P x y b h
  extension := fun U W hU hW f => coherentExtension P U W hU hW f
  extension_triple := by
    intro U W hU hW f p q r
    exact coherentExtension_triple_iff P U W hU hW f p q r
  extension_on := by
    intro U W hU hW f hf x hx
    exact coherentExtension_on_root P U W hU hW f hf x hx
  extension_id := by
    intro U hU
    exact coherentExtension_id P U hU
  extension_comp := by
    intro U W T hU hW hT f g
    exact coherentExtension_comp P U W T hU hW hT f g

end GluingEPPA.Steiner.InitialSites
