import GluingEPPA.Sparsening.TreeRootFactorization
import GluingEPPA.Sparsening.TreeIrreducibleSide

/-!
# Homomorphism-embeddings glued over a real upstairs free cut

A projection of a lifted free cut need not be a free cut of the old
structure. Accordingly, the source of every glued map below is the
ACTUAL upstairs free decomposition, and the two target trees are
identified only over an exact (possibly empty) root.

The code reuses the verified carrier and functional homomorphism
interfaces in TreeFreeCutMaps, TreeFreeCutHom, and TreePushoutExact.
The final theorem packages precisely the irreducible-test reflection
needed by the local-tree sparsening induction.
-/

namespace GluingEPPA.Sparsening.Tree

universe u v w t
variable {L : Nat → Type u} {F : Type t}
variable {P : Type v} {I X Y : Type w}
variable {R : RelStructure L P} {out : F → P → Set P}
variable {RI : RelStructure L I} {outI : F → I → Set I}
variable {RX : RelStructure L X} {outX : F → X → Set X}
variable {RY : RelStructure L Y} {outY : F → Y → Set Y}

/-- The map on a genuine source free cut: put each source side into its
own target tree, and then into the exact strong amalgam of the targets.
No agreement hypothesis is needed to DEFINE this total map. -/
noncomputable def glueFreeCutToPushout
    (d : UnaryFreeDecomposition R out)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (l : d.left → X) (r : d.right → Y) : P → PushoutCarrier ef.toFun eg.toFun :=
  glueFreeCutMap d
    (fun x => inclLeft ef.toFun eg.toFun (l x))
    (fun y => inclRight ef.toFun eg.toFun (r y))

/-- If the source-side maps agree THROUGH the prescribed exact root,
their images agree in the target pushout. -/
theorem root_images_agree
    (d : UnaryFreeDecomposition R out)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (l : d.left → X) (r : d.right → Y)
    (hroot : ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      ∃ i : I, l ⟨x, hxL⟩ = ef.toFun i ∧ r ⟨x, hxR⟩ = eg.toFun i)
    (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right) :
    inclLeft ef.toFun eg.toFun (l ⟨x, hxL⟩) =
      inclRight ef.toFun eg.toFun (r ⟨x, hxR⟩) := by
  obtain ⟨i, hl, hr⟩ := hroot x hxL hxR
  calc
    inclLeft ef.toFun eg.toFun (l ⟨x, hxL⟩) =
        inclLeft ef.toFun eg.toFun (ef.toFun i) := congrArg _ hl
    _ = inclRight ef.toFun eg.toFun (eg.toFun i) :=
        (inclRight_glued ef.toFun eg.toFun eg.injective i).symm
    _ = inclRight ef.toFun eg.toFun (r ⟨x, hxR⟩) :=
        congrArg _ hr.symm

/-- The glued map preserves every relation, including nullary relations,
without assuming that the projection of the source free cut is free. -/
theorem glueFreeCutToPushout_rel
    (d : UnaryFreeDecomposition R out)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (l : d.left → X) (r : d.right → Y)
    (hroot : ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      ∃ i : I, l ⟨x, hxL⟩ = ef.toFun i ∧ r ⟨x, hxR⟩ = eg.toFun i)
    (hLeft : ∀ {n} (t : L n) (xs : Fin n → d.left),
      R.rel t (fun i => (xs i).val) →
        RX.rel t (fun i => l (xs i)))
    (hRight : ∀ {n} (t : L n) (ys : Fin n → d.right),
      R.rel t (fun i => (ys i).val) →
        RY.rel t (fun i => r (ys i)))
    {n : Nat} (t : L n) (xs : Fin n → P) (ht : R.rel t xs) :
    (pushoutRelations ef.toFun eg.toFun RX RY).rel t
      (fun i => glueFreeCutToPushout d ef eg l r (xs i)) := by
  have hagree :
      ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
        inclLeft ef.toFun eg.toFun (l ⟨x, hxL⟩) =
          inclRight ef.toFun eg.toFun (r ⟨x, hxR⟩) :=
    root_images_agree d ef eg l r hroot
  simpa only [glueFreeCutToPushout] using
    (glueFreeCutMap_rel d
      (pushoutRelations ef.toFun eg.toFun RX RY)
      (fun x => inclLeft ef.toFun eg.toFun (l x))
      (fun y => inclRight ef.toFun eg.toFun (r y))
      hagree
      (by
        intro n t ys hy
        exact left_map_rel ef.toFun eg.toFun RX RY t
          (fun i => l (ys i)) (hLeft t ys hy))
      (by
        intro n t ys hy
        exact right_map_rel ef.toFun eg.toFun RX RY t
          (fun i => r (ys i)) (hRight t ys hy))
      t xs ht)

/-- The glued map preserves each member of every entire unary fibre.
The sides of the source free cut, not their projections, provide closure. -/
theorem glueFreeCutToPushout_unary_mem
    (d : UnaryFreeDecomposition R out)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (l : d.left → X) (r : d.right → Y)
    (hroot : ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      ∃ i : I, l ⟨x, hxL⟩ = ef.toFun i ∧ r ⟨x, hxR⟩ = eg.toFun i)
    (hLeft : ∀ (f : F) (x y : d.left),
      y.val ∈ out f x.val → l y ∈ outX f (l x))
    (hRight : ∀ (f : F) (x y : d.right),
      y.val ∈ out f x.val → r y ∈ outY f (r x))
    (f : F) (x y : P) (hy : y ∈ out f x) :
    glueFreeCutToPushout d ef eg l r y ∈
      pushoutOutput ef.toFun eg.toFun outX outY f
        (glueFreeCutToPushout d ef eg l r x) := by
  have hagree :
      ∀ (z : P) (hzL : z ∈ d.left) (hzR : z ∈ d.right),
        inclLeft ef.toFun eg.toFun (l ⟨z, hzL⟩) =
          inclRight ef.toFun eg.toFun (r ⟨z, hzR⟩) :=
    root_images_agree d ef eg l r hroot
  simpa only [glueFreeCutToPushout] using
    (glueFreeCutMap_unary_mem d
      (pushoutOutput ef.toFun eg.toFun outX outY)
      (fun z => inclLeft ef.toFun eg.toFun (l z))
      (fun z => inclRight ef.toFun eg.toFun (r z))
      hagree
      (by
        intro f a b hb
        exact left_map_unary ef.toFun eg.toFun outX outY f
          (l a) (l b) (hLeft f a b hb))
      (by
        intro f a b hb
        exact right_map_unary ef.toFun eg.toFun outX outY f
          (r a) (r b) (hRight f a b hb))
      f x y hy)

/-- On an irreducible closed source test, the glued map is an exact
embedding whenever the corresponding side map is exact on that test.
This avoids imposing global injectivity on a homomorphism-embedding. -/
theorem glueFreeCutToPushout_exact_on_irreducible
    (d : UnaryFreeDecomposition R out)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (l : d.left → X) (r : d.right → Y)
    (hroot : ∀ (x : P) (hxL : x ∈ d.left) (hxR : x ∈ d.right),
      ∃ i : I, l ⟨x, hxL⟩ = ef.toFun i ∧ r ⟨x, hxR⟩ = eg.toFun i)
    (S : Set P)
    (hclosed : UnaryClosed out (fun p => p ∈ S))
    (hirr : IsIrreducible
      (inducedRelations R S) (inducedUnary out S))
    (hLeft : ∀ (hS : S ⊆ d.left),
      ∃ e : ExactUnaryEmbedding
          (inducedRelations R S) (inducedUnary out S) RX outX,
        ∀ z : S, e.toFun z = l ⟨z.val, hS z.property⟩)
    (hRight : ∀ (hS : S ⊆ d.right),
      ∃ e : ExactUnaryEmbedding
          (inducedRelations R S) (inducedUnary out S) RY outY,
        ∀ z : S, e.toFun z = r ⟨z.val, hS z.property⟩) :
    ∃ e : ExactUnaryEmbedding
        (inducedRelations R S) (inducedUnary out S)
        (pushoutRelations ef.toFun eg.toFun RX RY)
        (pushoutOutput ef.toFun eg.toFun outX outY),
      ∀ z : S, e.toFun z = glueFreeCutToPushout d ef eg l r z.val := by
  rcases irreducible_subset_one_side R out d S hclosed hirr with hs | hs
  · obtain ⟨e, he⟩ := hLeft hs
    let inc := leftExactEmbedding RI outI RX outX RY outY ef eg
    refine ⟨inc.comp e, ?_⟩
    intro z
    change inclLeft ef.toFun eg.toFun (e.toFun z) =
      glueFreeCutToPushout d ef eg l r z.val
    rw [he z]
    exact (glueFreeCutMap_left d
      (fun x => inclLeft ef.toFun eg.toFun (l x))
      (fun y => inclRight ef.toFun eg.toFun (r y))
      z.val (hs z.property)).symm
  · obtain ⟨e, he⟩ := hRight hs
    let inc := rightExactEmbedding RI outI RX outX RY outY ef eg
    refine ⟨inc.comp e, ?_⟩
    intro z
    change inclRight ef.toFun eg.toFun (e.toFun z) =
      glueFreeCutToPushout d ef eg l r z.val
    rw [he z]
    exact (glueFreeCutMap_right d
      (fun x => inclLeft ef.toFun eg.toFun (l x))
      (fun y => inclRight ef.toFun eg.toFun (r y))
      (root_images_agree d ef eg l r hroot)
      z.val (hs z.property)).symm

end GluingEPPA.Sparsening.Tree
