import GluingEPPA.Sparsening.TreeHomEmbeddingClosedCodomain

/-!
# Glue two projected old-image trees along an upstairs free cut

The induction reduces proper upstairs source sides to old CLOSED images
under an arbitrary homomorphism-embedding. Each old side image maps
homomorphism-embeddably into a strict tree. An old complete-J closed root
inside both images gives exact target root embeddings. We then combine
the two target trees and the upstairs free-cut map.

No injectivity of the projection and no free decomposition of its
OLD image is ever required. The resulting target is finite when the two
input targets are finite. This abstract theorem isolates all non-geometric
reasoning needed for the canonical Boolean-atlas induction.
-/

namespace GluingEPPA.Sparsening.Tree
universe u v t
variable {L : Nat → Type u} {F : Type t}
variable {P B A X Y : Type v}

/-- A complete actual binary J on an entire structure prevents every
proper unary free decomposition, including for the empty structure. -/
theorem irreducible_of_complete_J
    (R : RelStructure (WithJ L) P) (out : F → P → Set P)
    (hJ : IsJClique R Set.univ) :
    IsIrreducible R out := by
  classical
  constructor
  intro d
  obtain ⟨p, hp⟩ : ∃ p : P, p ∉ d.left := by
    by_contra h
    push Not at h
    exact d.left_proper (Set.eq_univ_of_forall h)
  obtain ⟨q, hq⟩ : ∃ q : P, q ∉ d.right := by
    by_contra h
    push Not at h
    exact d.right_proper (Set.eq_univ_of_forall h)
  have hj := hJ q (Set.mem_univ q) p (Set.mem_univ p)
  rcases d.rel_local (Sum.inr (⟨(), rfl⟩ : JSymbol 2))
      (JPair q p) hj with hl | hr
  · exact hp (by simpa [JPair] using hl (1 : Fin 2))
  · exact hq (by simpa [JPair] using hr (0 : Fin 2))

/-- The induction's abstract gluing statement. The source is decomposed
freely UPSTAIRS and projected homomorphism-embeddably into an old
structure. The old images of the proper sides need NOT form a free
amalgam. The root is any old CLOSED J-clique lying in both images
and containing the projection of the actual upstairs overlap. -/
theorem FullATree.glueProjectedRoot
    (RP : RelStructure (WithJ L) P) (outP : F → P → Set P)
    (RB : RelStructure (WithJ L) B) (outB : F → B → Set B)
    (RA : RelStructure (WithJ L) A) (outA : F → A → Set A)
    (d : UnaryFreeDecomposition RP outP)
    (p : UnaryHomEmbedding RP outP RB outB)
    (SL SR root : Set B)
    (hSL : UnaryClosed outB (fun b => b ∈ SL))
    (hSR : UnaryClosed outB (fun b => b ∈ SR))
    (hRoot : UnaryClosed outB (fun b => b ∈ root))
    (hLmem : ∀ z : d.left, p.toFun z.val ∈ SL)
    (hRmem : ∀ z : d.right, p.toFun z.val ∈ SR)
    (hRootL : root ⊆ SL)
    (hRootR : root ⊆ SR)
    (hOverlap : ∀ (z : P), z ∈ d.left → z ∈ d.right →
      p.toFun z ∈ root)
    (hJ : IsJClique (inducedRelations RB root) Set.univ)
    (RX : RelStructure (WithJ L) X) (outX : F → X → Set X)
    (RY : RelStructure (WithJ L) Y) (outY : F → Y → Set Y)
    (treeX : FullATree RA outA RX outX)
    (treeY : FullATree RA outA RY outY)
    (hx : UnaryHomEmbedding
      (inducedRelations RB SL) (inducedUnary outB SL) RX outX)
    (hy : UnaryHomEmbedding
      (inducedRelations RB SR) (inducedUnary outB SR) RY outY) :
    ∃ (V : Type v) (RV : RelStructure (WithJ L) V)
      (outV : F → V → Set V),
      FullATree RA outA RV outV ∧
      Nonempty (UnaryHomEmbedding RP outP RV outV) := by
  classical
  let pL : UnaryHomEmbedding
      (inducedRelations RP d.left) (inducedUnary outP d.left)
      (inducedRelations RB SL) (inducedUnary outB SL) :=
    (p.restrictClosed d.left d.left_closed).intoClosedCodomain
      SL hSL hLmem
  let pR : UnaryHomEmbedding
      (inducedRelations RP d.right) (inducedUnary outP d.right)
      (inducedRelations RB SR) (inducedUnary outB SR) :=
    (p.restrictClosed d.right d.right_closed).intoClosedCodomain
      SR hSR hRmem
  let l := hx.comp pL
  let r := hy.comp pR
  have hIrr : IsIrreducible
      (inducedRelations RB root) (inducedUnary outB root) :=
    irreducible_of_complete_J _ _ hJ
  let inclL := exactSubsetIntoSide (R := RB) (out := outB)
    root SL hRootL hRoot
  let inclR := exactSubsetIntoSide (R := RB) (out := outB)
    root SR hRootR hRoot
  obtain ⟨ef, hef⟩ := hx.exact_afterExact inclL hIrr
  obtain ⟨eg, heg⟩ := hy.exact_afterExact inclR hIrr
  have hAgree : ∀ (z : P) (hzL : z ∈ d.left) (hzR : z ∈ d.right),
      ∃ i : root, l.toFun ⟨z, hzL⟩ = ef.toFun i ∧
        r.toFun ⟨z, hzR⟩ = eg.toFun i := by
    intro z hzL hzR
    let w : root := ⟨p.toFun z, hOverlap z hzL hzR⟩
    refine ⟨w, ?_, ?_⟩
    · calc
        l.toFun ⟨z, hzL⟩ =
          hx.toFun (⟨p.toFun z, hLmem ⟨z, hzL⟩⟩ : SL) := rfl
        _ = ef.toFun w := by
          have heq : (⟨p.toFun z, hLmem ⟨z, hzL⟩⟩ : SL) =
              inclL.toFun w := Subtype.ext rfl
          rw [heq]
          exact (hef w).symm
    · calc
        r.toFun ⟨z, hzR⟩ =
          hy.toFun (⟨p.toFun z, hRmem ⟨z, hzR⟩⟩ : SR) := rfl
        _ = eg.toFun w := by
          have heq : (⟨p.toFun z, hRmem ⟨z, hzR⟩⟩ : SR) =
              inclR.toFun w := Subtype.ext rfl
          rw [heq]
          exact (heg w).symm
  refine ⟨PushoutCarrier ef.toFun eg.toFun,
    pushoutRelations ef.toFun eg.toFun RX RY,
    pushoutOutput ef.toFun eg.toFun outX outY, ?_⟩
  exact FullATree.glueHomEmbedding RP outP d
    (inducedRelations RB root) (inducedUnary outB root)
    RA outA RX outX RY outY treeX treeY ef eg hJ l r hAgree

end GluingEPPA.Sparsening.Tree
