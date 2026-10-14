import GluingEPPA.Sparsening.TreeJCliqueRoot

/-!
# Factor a closed root through one full A-block of a strict tree

A local separator root is mapped into a tree by an *exact* embedding.
When its range is a complete auxiliary-J clique, the previously verified
tree-clique theorem finds one full A-block containing the range.
This file proves that the resulting set inclusion factors as an actual
exact unary/relational embedding into A. In particular it preserves
all full unary output fibres rather than just their forward images.

No arbitrary irreducibility-transport theorem and no instance of the
sparsening theorem is used here.
-/

namespace GluingEPPA.Sparsening.Tree

universe u v t
variable {L : Nat → Type u} {F : Type t}
variable {I A V : Type v}

namespace ExactUnaryEmbedding

/-- An exact embedding into V whose image lies in a second exact
embedding A -> V uniquely pulls back to an exact embedding into A. -/
noncomputable def factor_through
    {RI : RelStructure L I} {RA : RelStructure L A}
    {RV : RelStructure L V}
    {outI : F → I → Set I} {outA : F → A → Set A}
    {outV : F → V → Set V}
    (root : ExactUnaryEmbedding RI outI RV outV)
    (block : ExactUnaryEmbedding RA outA RV outV)
    (h : ∀ i : I, ∃ a : A, block.toFun a = root.toFun i) :
    ExactUnaryEmbedding RI outI RA outA := by
  classical
  let delta : I → A := fun i => Classical.choose (h i)
  have hdelta (i : I) : block.toFun (delta i) = root.toFun i :=
    Classical.choose_spec (h i)
  refine
    { toFun := delta
      injective := ?_
      rel_iff := ?_
      out_eq := ?_ }
  · intro i j hij
    apply root.injective
    calc
      root.toFun i = block.toFun (delta i) := (hdelta i).symm
      _ = block.toFun (delta j) := congrArg block.toFun hij
      _ = root.toFun j := hdelta j
  · intro n r xs
    have heq :
        (fun k : Fin n => block.toFun (delta (xs k))) =
          (fun k : Fin n => root.toFun (xs k)) := by
      funext k
      exact hdelta (xs k)
    calc
      RA.rel r (fun k => delta (xs k)) ↔
        RV.rel r (fun k => block.toFun (delta (xs k))) :=
          (block.rel_iff r (fun k => delta (xs k))).symm
      _ ↔ RV.rel r (fun k => root.toFun (xs k)) := by rw [heq]
      _ ↔ RI.rel r xs := root.rel_iff r xs
  · intro f z
    apply Set.ext
    intro x
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hroot : root.toFun i ∈ outV f (root.toFun z) := by
        rw [← root.out_eq f z]
        exact ⟨i, hi, rfl⟩
      have hblock :
          block.toFun (delta i) ∈ block.toFun '' outA f (delta z) := by
        rw [block.out_eq f (delta z)]
        simpa only [hdelta i, hdelta z] using hroot
      obtain ⟨a, ha, heq⟩ := hblock
      have hae : a = delta i := block.injective heq
      simpa only [hae] using ha
    · intro hx
      have hblock : block.toFun x ∈
          outV f (block.toFun (delta z)) := by
        rw [← block.out_eq f (delta z)]
        exact ⟨x, hx, rfl⟩
      have hroot : block.toFun x ∈ root.toFun '' outI f z := by
        rw [root.out_eq f z]
        simpa only [hdelta z] using hblock
      obtain ⟨i, hi, heq⟩ := hroot
      have hdi : delta i = x :=
        block.injective ((hdelta i).trans heq)
      exact ⟨i, hi, hdi⟩

/-- The factored embedding commutes literally with its two source maps. -/
theorem factor_through_spec
    {RI : RelStructure L I} {RA : RelStructure L A}
    {RV : RelStructure L V}
    {outI : F → I → Set I} {outA : F → A → Set A}
    {outV : F → V → Set V}
    (root : ExactUnaryEmbedding RI outI RV outV)
    (block : ExactUnaryEmbedding RA outA RV outV)
    (h : ∀ i : I, ∃ a : A, block.toFun a = root.toFun i)
    (i : I) :
    block.toFun ((factor_through root block h).toFun i) =
      root.toFun i := by
  classical
  change block.toFun (Classical.choose (h i)) = root.toFun i
  exact Classical.choose_spec (h i)

end ExactUnaryEmbedding

/-- A complete-J root of a strict A-tree embeds into a full A-block,
with an exactly commuting triangle and *complete unary fibres*.
This is the precise interface needed to attach two tree targets. -/
theorem FullATree.JRoot_factorization
    {RI : RelStructure (WithJ L) I} {RA : RelStructure (WithJ L) A}
    {RV : RelStructure (WithJ L) V}
    {outI : F → I → Set I} {outA : F → A → Set A}
    {outV : F → V → Set V}
    (tree : FullATree RA outA RV outV)
    (root : ExactUnaryEmbedding RI outI RV outV)
    (hJ : IsJClique RV (Set.range root.toFun)) :
    ∃ (delta : ExactUnaryEmbedding RI outI RA outA)
      (block : ExactUnaryEmbedding RA outA RV outV),
      ∀ i : I, block.toFun (delta.toFun i) = root.toFun i := by
  classical
  obtain ⟨block, hblock⟩ :=
    FullATree.JClique_contained_in_A RA outA RV outV tree
      (Set.range root.toFun) hJ
  have h : ∀ i : I, ∃ a : A,
      block.toFun a = root.toFun i := by
    intro i
    exact hblock ⟨i, rfl⟩
  let delta := ExactUnaryEmbedding.factor_through root block h
  refine ⟨delta, block, ?_⟩
  intro i
  exact ExactUnaryEmbedding.factor_through_spec root block h i


/-- Strict full-A trees admit gluing along any exact pair of embeddings
whose common root is a J-clique in both trees. The J containment theorem
automatically supplies a full A-block on each side. This is the literal
target constructor needed by the local separator induction. -/
theorem FullATree.glue_JRoots
    {X Y : Type v}
    (RI : RelStructure (WithJ L) I) (outI : F → I → Set I)
    (RA : RelStructure (WithJ L) A) (outA : F → A → Set A)
    (RX : RelStructure (WithJ L) X) (outX : F → X → Set X)
    (RY : RelStructure (WithJ L) Y) (outY : F → Y → Set Y)
    (treeX : FullATree RA outA RX outX)
    (treeY : FullATree RA outA RY outY)
    (f : ExactUnaryEmbedding RI outI RX outX)
    (g : ExactUnaryEmbedding RI outI RY outY)
    (hJX : IsJClique RX (Set.range f.toFun))
    (hJY : IsJClique RY (Set.range g.toFun)) :
    FullATree RA outA
      (pushoutRelations f.toFun g.toFun RX RY)
      (pushoutOutput f.toFun g.toFun outX outY) := by
  obtain ⟨deltaX, blockX, hf⟩ :=
    FullATree.JRoot_factorization treeX f hJX
  obtain ⟨deltaY, blockY, hg⟩ :=
    FullATree.JRoot_factorization treeY g hJY
  have hfx : (blockX.comp deltaX).toFun = f.toFun := by
    funext i
    exact hf i
  have hgy : (blockY.comp deltaY).toFun = g.toFun := by
    funext i
    exact hg i
  have hTree : FullATree RA outA
      (pushoutRelations (blockX.comp deltaX).toFun
        (blockY.comp deltaY).toFun RX RY)
      (pushoutOutput (blockX.comp deltaX).toFun
        (blockY.comp deltaY).toFun outX outY) :=
    FullATree.glue RI outI RX outX RY outY
      treeX treeY deltaX deltaY blockX blockY
  rw [← hfx, ← hgy]
  exact hTree

end GluingEPPA.Sparsening.Tree
