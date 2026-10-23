import GluingEPPA.Steiner.DiagramRootWitness

/-!
# Coherent EPPA for finite partial Steiner triple systems

This is the assembled theorem for the diagram construction: a finite
partial Steiner triple system, a closed induced copy of the input, and
a coherent family of automorphisms extending all partial automorphisms
between its closed subsystems.

The finite quotient, actual root copy and its closure, the concrete
relabelling action, the uniform pointwise extension calculation, and
the composition law are all proved in preceding modules. This file
packages those statements without introducing additional axioms.
-/

namespace GluingEPPA.Steiner.InitialSites

open EdgeGraph EdgeGraph.RecursiveRecord
attribute [local instance] Classical.propDecidable

universe u
variable {A : Type u} [Fintype A] [LinearOrder A] [DecidableEq A]

/-- A finite partial Steiner witness, together with a closed induced
embedding and a coherent family of chosen extensions for all partial
automorphisms between closed subsets of the input. -/
structure CoherentSteinerWitness (P : Input A) where
  B : Type u
  finiteB : Finite B
  triple : B → B → B → Prop
  triple_unique : ∀ p q r s, triple p q r → triple p q s → r = s
  triple_swap : ∀ p q r, triple p q r → triple q p r
  triple_rotate : ∀ p q r, triple p q r → triple q r p
  triple_distinct : ∀ p q r, triple p q r →
    p ≠ q ∧ p ≠ r ∧ q ≠ r
  embed : A → B
  embed_injective : Function.Injective embed
  embed_triple_iff : ∀ x y z,
    triple (embed x) (embed y) (embed z) ↔ P.triple x y z
  embed_closed : ∀ x y (b : B), triple (embed x) (embed y) b →
    ∃ z, P.triple x y z ∧ b = embed z
  extension : ∀ (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A)),
    ({x : A // x ∈ U} ≃ {x : A // x ∈ W}) → Equiv.Perm B
  extension_preserves : ∀ (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (p q r : B),
    triple p q r → triple ((extension U W hU hW f) p)
      ((extension U W hU hW f) q)
      ((extension U W hU hW f) r)
  extension_on : ∀ (U W : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W}),
    (∀ (x y z : A) (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U),
      P.triple x y z ↔ P.triple (f ⟨x,hx⟩).val
        (f ⟨y,hy⟩).val (f ⟨z,hz⟩).val) →
    ∀ (x : A) (hx : x ∈ U),
      (extension U W hU hW f) (embed x) =
        embed (f ⟨x,hx⟩).val
  extension_id : ∀ (U : Finset A) (hU : Closed P.triple (U : Set A)),
    extension U U hU hU (Equiv.refl {x : A // x ∈ U}) =
      Equiv.refl B
  extension_comp : ∀ (U W T : Finset A)
    (hU : Closed P.triple (U : Set A))
    (hW : Closed P.triple (W : Set A))
    (hT : Closed P.triple (T : Set A))
    (f : {x : A // x ∈ U} ≃ {x : A // x ∈ W})
    (g : {x : A // x ∈ W} ≃ {x : A // x ∈ T}),
    (extension U W hU hW f).trans (extension W T hW hT g) =
      extension U T hU hT (f.trans g)

/-- Assemble the actual recursive diagram's free quotient into
a finite coherent Steiner EPPA witness. -/
noncomputable def coherentSteinerWitness (P : Input A) :
    CoherentSteinerWitness P := by
  classical
  letI : Fintype (Edge P.triple) := Fintype.ofFinite _
  letI : DecidableEq (Edge P.triple) := Classical.decEq _
  exact {
    B := realizedPoint (graph P.triple) (localDiagram P)
    finiteB := by infer_instance
    triple := realizedTriple (graph P.triple) (localDiagram P)
    triple_unique := realizedTriple_unique (graph P.triple) (localDiagram P)
    triple_swap := realizedTriple_swap (graph P.triple) (localDiagram P)
    triple_rotate := realizedTriple_rotate (graph P.triple) (localDiagram P)
    triple_distinct := realizedTriple_distinct (graph P.triple) (localDiagram P)
    embed := rootEmbedding P
    embed_injective := rootEmbedding_injective P
    embed_triple_iff := rootEmbedding_triple_iff P
    embed_closed := rootEmbedding_closed P
    extension := fun U W hU hW f => coherentExtension P U W hU hW f
    extension_preserves := fun U W hU hW f p q r h =>
      coherentExtension_preserves_triple P U W hU hW f p q r h
    extension_on := fun U W hU hW f hf x hx =>
      coherentExtension_on_root P U W hU hW f hf x hx
    extension_id := fun U hU => coherentExtension_id P U hU
    extension_comp := fun U W T hU hW hT f g =>
      coherentExtension_comp P U W T hU hW hT f g
  }

/-- Every finite partial Steiner triple system has a finite witness
with a closed induced copy and coherent extensions of all partial
automorphisms of its closed substructures. -/
theorem coherentSteinerEPPA (P : Input A) :
    Nonempty (CoherentSteinerWitness P) :=
  ⟨coherentSteinerWitness P⟩

end GluingEPPA.Steiner.InitialSites
