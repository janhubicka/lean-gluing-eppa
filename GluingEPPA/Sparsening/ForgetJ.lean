import GluingEPPA.Sparsening.TreeHomEmbeddingRestrict
import GluingEPPA.Sparsening.TreeFullA

/-!
# Forgetting the auxiliary binary relation

Closed sets and unary fibres are unchanged. An irreducible reduct is
still irreducible in the expansion: any expanded free cut would also
be a free cut after reduction. Thus exactness on irreducibles survives
reduction, in the direction required by the sparsening theorem.
-/

namespace GluingEPPA.Sparsening

universe u v w t
variable {L : Nat → Type u} {F : Type t}
variable {A : Type v} {B : Type w}

/-- Retain exactly the original relation symbols of WithJ L. -/
def forgetJRelations (R : RelStructure (WithJ L) A) : RelStructure L A where
  rel r xs := R.rel (Sum.inl r) xs

/-- Forgetting a relation cannot destroy an existing free-cut certificate. -/
def UnaryFreeDecomposition.forgetJ
    {R : RelStructure (WithJ L) A} {out : F → A → Set A}
    (d : UnaryFreeDecomposition R out) :
    UnaryFreeDecomposition (forgetJRelations R) out where
  left := d.left
  right := d.right
  left_closed := d.left_closed
  right_closed := d.right_closed
  cover := d.cover
  left_proper := d.left_proper
  right_proper := d.right_proper
  rel_local r xs hr := d.rel_local (Sum.inl r) xs hr
  func_cross_empty := d.func_cross_empty

/-- The direction needed for exactness and faithfulness in the reduct. -/
theorem irreducible_expand_J (R : RelStructure (WithJ L) A)
    (out : F → A → Set A) (h : IsIrreducible (forgetJRelations R) out) :
    IsIrreducible R out :=
  ⟨fun d => h.false d.forgetJ⟩

/-- Exact embeddings retain their map and complete unary-fibre equation. -/
def Tree.ExactUnaryEmbedding.forgetJ
    {RA : RelStructure (WithJ L) A} {RB : RelStructure (WithJ L) B}
    {outA : F → A → Set A} {outB : F → B → Set B}
    (e : Tree.ExactUnaryEmbedding RA outA RB outB) :
    Tree.ExactUnaryEmbedding (forgetJRelations RA) outA (forgetJRelations RB) outB where
  toFun := e.toFun
  injective := e.injective
  rel_iff r xs := e.rel_iff (Sum.inl r) xs
  out_eq := e.out_eq

/-- No global injectivity is required to reduce a homomorphism-embedding. -/
def Tree.UnaryHomEmbedding.forgetJ
    {RA : RelStructure (WithJ L) A} {RB : RelStructure (WithJ L) B}
    {outA : F → A → Set A} {outB : F → B → Set B}
    (h : Tree.UnaryHomEmbedding RA outA RB outB) :
    Tree.UnaryHomEmbedding (forgetJRelations RA) outA (forgetJRelations RB) outB where
  toFun := h.toFun
  rel_map r xs hr := h.rel_map (Sum.inl r) xs hr
  unary_map := h.unary_map
  exact_on_irred := by
    intro S hS hirr
    have hi : IsIrreducible (inducedRelations RA S) (inducedUnary outA S) :=
      irreducible_expand_J (inducedRelations RA S) (inducedUnary outA S) hirr
    obtain ⟨e, he⟩ := h.exact_on_irred S hS hi
    exact ⟨e.forgetJ, he⟩

/-- All expanded automorphisms are still automorphisms after reduction. -/
def OrbitAtlas.Aut.forgetJ
    {R : RelStructure (WithJ L) A} {out : F → A → Set A}
    (h : OrbitAtlas.Aut R out) : OrbitAtlas.Aut (forgetJRelations R) out where
  perm := h.perm
  rel_iff r xs := h.rel_iff (Sum.inl r) xs
  unary_iff := h.unary_iff

/-- The same recursive amalgamation, maps and carrier give a strict
full-A tree after reduction. When the original A is irreducible this
is a tree amalgam of A-copies in the manuscript's convention. -/
theorem Tree.FullATree.forgetJ
    {RA : RelStructure (WithJ L) A} {outA : F → A → Set A}
    {V : Type v} {RV : RelStructure (WithJ L) V} {outV : F → V → Set V}
    (tree : Tree.FullATree RA outA RV outV) :
    Tree.FullATree (forgetJRelations RA) outA (forgetJRelations RV) outV := by
  induction tree with
  | copy RV outV e he =>
      exact .copy (forgetJRelations RV) outV e.forgetJ he
  | glue RI outI RX outX RY outY hX hY δX δY αX αY ihX ihY =>
      exact Tree.FullATree.glue (forgetJRelations RI) outI
        (forgetJRelations RX) outX (forgetJRelations RY) outY ihX ihY
        δX.forgetJ δY.forgetJ αX.forgetJ αY.forgetJ

end GluingEPPA.Sparsening
