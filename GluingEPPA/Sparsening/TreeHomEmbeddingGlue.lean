import GluingEPPA.Sparsening.TreeHomEmbedding

/-!
# Gluing homomorphism-embeddings along an actual source free cut

The two target trees are glued over an exact common root. The source map
is assembled across the ACTUAL upstairs free cut; in particular the
induced structure on the projected old image is NOT assumed free.

This statement consumes the local exact-test gluing already verified in
TreeFreeCutPushoutHom, and the closed irreducible image/composition API.
-/
namespace GluingEPPA.Sparsening.Tree

universe u v w x t
variable {L : Nat → Type u} {F : Type t}
variable {P : Type v} {I X Y : Type w}
variable {R : RelStructure L P} {out : F → P → Set P}
variable {RI : RelStructure L I} {outI : F → I → Set I}
variable {RX : RelStructure L X} {outX : F → X → Set X}
variable {RY : RelStructure L Y} {outY : F → Y → Set Y}

/-- If S is closed and lies inside T, then S embeds exactly into the
structure induced on T, even when T is not assumed irreducible. -/
def exactSubsetIntoSide (S T : Set P)
    (hsub : S ⊆ T)
    (hclosed : UnaryClosed out (fun p => p ∈ S)) :
    ExactUnaryEmbedding (inducedRelations R S) (inducedUnary out S)
      (inducedRelations R T) (inducedUnary out T) where
  toFun := fun z => ⟨z.val, hsub z.property⟩
  injective := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun q : T => (q : P)) hab
  rel_iff := by
    intro n r xs
    exact Iff.rfl
  out_eq := by
    intro f a
    ext b
    constructor
    · rintro ⟨z, hz, heq⟩
      have hb : z.val = b.val := congrArg Subtype.val heq
      change b.val ∈ out f a.val
      exact hb ▸ hz
    · intro hb
      have hs : b.val ∈ S := hclosed f a.val b.val a.property hb
      exact ⟨⟨b.val, hs⟩, hb, Subtype.ext rfl⟩

namespace UnaryHomEmbedding

/-- An arbitrary homomorphism-embedding is exact after an exact embedding
from an irreducible source, via its closed induced range. -/
theorem exact_afterExact
    {A : Type v} {B : Type w} {C : Type x}
    {RA : RelStructure L A} {RB : RelStructure L B}
    {RC : RelStructure L C}
    {outA : F → A → Set A} {outB : F → B → Set B}
    {outC : F → C → Set C}
    (h : UnaryHomEmbedding RB outB RC outC)
    (e : ExactUnaryEmbedding RA outA RB outB)
    (hirr : IsIrreducible RA outA) :
    ∃ k : ExactUnaryEmbedding RA outA RC outC,
      ∀ a : A, k.toFun a = h.toFun (e.toFun a) := by
  let S : Set B := Set.range e.toFun
  have hS : UnaryClosed outB (fun b => b ∈ S) := e.range_closed
  have hirrS : IsIrreducible (inducedRelations RB S)
      (inducedUnary outB S) := e.range_irreducible hirr
  obtain ⟨g, hg⟩ := h.exact_on_irred S hS hirrS
  refine ⟨g.comp e.toClosedRange, ?_⟩
  intro a
  change g.toFun (⟨e.toFun a, ⟨a, rfl⟩⟩ : S) = h.toFun (e.toFun a)
  exact hg ⟨e.toFun a, ⟨a, rfl⟩⟩

end UnaryHomEmbedding

/-- Gluing homomorphism-embeddings over a common exact root preserves the
homomorphism-embedding property, even when the projections of the source
pieces have additional cross-relations. -/
noncomputable def unaryHomEmbedding_glueFreeCut
    (d : UnaryFreeDecomposition R out)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (l : UnaryHomEmbedding
      (inducedRelations R d.left) (inducedUnary out d.left) RX outX)
    (r : UnaryHomEmbedding
      (inducedRelations R d.right) (inducedUnary out d.right) RY outY)
    (hroot : ∀ (z : P) (hzL : z ∈ d.left) (hzR : z ∈ d.right),
      ∃ i : I, l.toFun ⟨z, hzL⟩ = ef.toFun i ∧
        r.toFun ⟨z, hzR⟩ = eg.toFun i) :
    UnaryHomEmbedding R out
      (pushoutRelations ef.toFun eg.toFun RX RY)
      (pushoutOutput ef.toFun eg.toFun outX outY) where
  toFun := glueFreeCutToPushout d ef eg l.toFun r.toFun
  rel_map := by
    intro n t xs ht
    exact glueFreeCutToPushout_rel d ef eg l.toFun r.toFun hroot
      (by
        intro n t ys hy
        exact l.rel_map t ys hy)
      (by
        intro n t ys hy
        exact r.rel_map t ys hy)
      t xs ht
  unary_map := by
    intro f a b hb
    exact glueFreeCutToPushout_unary_mem d ef eg l.toFun r.toFun hroot
      (by
        intro f a b hab
        exact l.unary_map f a b hab)
      (by
        intro f a b hab
        exact r.unary_map f a b hab)
      f a b hb
  exact_on_irred := by
    intro S hclosed hirr
    refine glueFreeCutToPushout_exact_on_irreducible
      d ef eg l.toFun r.toFun hroot S hclosed hirr ?_ ?_
    · intro hsub
      let e := exactSubsetIntoSide (R := R) (out := out)
        S d.left hsub hclosed
      obtain ⟨k, hk⟩ := l.exact_afterExact e hirr
      exact ⟨k, hk⟩
    · intro hsub
      let e := exactSubsetIntoSide (R := R) (out := out)
        S d.right hsub hclosed
      obtain ⟨k, hk⟩ := r.exact_afterExact e hirr
      exact ⟨k, hk⟩

end GluingEPPA.Sparsening.Tree
