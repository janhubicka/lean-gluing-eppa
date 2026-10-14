import GluingEPPA.Sparsening.TreePushoutExact

/-!
# Genuine strong amalgamation of finite unary relational structures

The earlier exact-overlap lemmas are packaged as actual embeddings. Their
images are closed under entire unary fibres and cover the new structure;
the contributed interpretations have a genuine free-amalgam certificate.
This follows the verified structural organization of
AllThoseEPPA/TreeLikeAmalgamEmbeddings.lean and
AllThoseEPPA/TreeLikeAmalgamFree.lean, without assuming any EPPA conclusion.
-/
namespace GluingEPPA.Sparsening.Tree
universe u v w x t
variable {L : Nat → Type u} {F : Type t}
variable {I : Type v} {X : Type w} {Y : Type x}

/-- The canonical left inclusion reflects every relation and has equality
of complete unary-fibre images, hence is an exact embedding. -/
noncomputable def leftExactEmbedding
    (RI : RelStructure L I) (outI : F → I → Set I)
    (RX : RelStructure L X) (outX : F → X → Set X)
    (RY : RelStructure L Y) (outY : F → Y → Set Y)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY) :
    ExactUnaryEmbedding RX outX
      (pushoutRelations ef.toFun eg.toFun RX RY)
      (pushoutOutput ef.toFun eg.toFun outX outY) where
  toFun := inclLeft ef.toFun eg.toFun
  injective := inclLeft_injective ef.toFun eg.toFun
  rel_iff r xs :=
    left_rel_iff RI outI RX outX RY outY ef eg r xs
  out_eq h x :=
    left_unary_image_eq RI outI RX outX RY outY ef eg h x

/-- The right inclusion is also an exact embedding, including points in
the common interface where it is represented by a left-hand vertex. -/
noncomputable def rightExactEmbedding
    (RI : RelStructure L I) (outI : F → I → Set I)
    (RX : RelStructure L X) (outX : F → X → Set X)
    (RY : RelStructure L Y) (outY : F → Y → Set Y)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY) :
    ExactUnaryEmbedding RY outY
      (pushoutRelations ef.toFun eg.toFun RX RY)
      (pushoutOutput ef.toFun eg.toFun outX outY) where
  toFun := inclRight ef.toFun eg.toFun
  injective := inclRight_injective ef.toFun eg.toFun
    ef.injective eg.injective
  rel_iff r ys :=
    right_rel_iff RI outI RX outX RY outY ef eg r ys
  out_eq h y :=
    right_unary_image_eq RI outI RX outX RY outY ef eg h y

/-- Properness is the only extra hypothesis: both sides have at least one
vertex outside the gluing interface. The resulting certified cut contains
ALL relation tuples on one side, preserves whole unary fibres and has no
mixed-side interpretation. -/
noncomputable def pushoutFreeDecomposition
    (RI : RelStructure L I) (outI : F → I → Set I)
    (RX : RelStructure L X) (outX : F → X → Set X)
    (RY : RelStructure L Y) (outY : F → Y → Set Y)
    (ef : ExactUnaryEmbedding RI outI RX outX)
    (eg : ExactUnaryEmbedding RI outI RY outY)
    (hLeftExtra : ∃ x : X, x ∉ Set.range ef.toFun)
    (hRightExtra : ∃ y : Y, y ∉ Set.range eg.toFun) :
    UnaryFreeDecomposition
      (pushoutRelations ef.toFun eg.toFun RX RY)
      (pushoutOutput ef.toFun eg.toFun outX outY) := by
  classical
  let left : ExactUnaryEmbedding RX outX
      (pushoutRelations ef.toFun eg.toFun RX RY)
      (pushoutOutput ef.toFun eg.toFun outX outY) :=
    leftExactEmbedding RI outI RX outX RY outY ef eg
  let right : ExactUnaryEmbedding RY outY
      (pushoutRelations ef.toFun eg.toFun RX RY)
      (pushoutOutput ef.toFun eg.toFun outX outY) :=
    rightExactEmbedding RI outI RX outX RY outY ef eg
  refine
    { left := Set.range left.toFun
      right := Set.range right.toFun
      left_closed := ?_
      right_closed := ?_
      cover := ?_
      left_proper := ?_
      right_proper := ?_
      rel_local := ?_
      func_cross_empty := ?_ }
  · intro h p q hp hq
    obtain ⟨x, rfl⟩ := hp
    have hm : q ∈ left.toFun '' outX h x := by
      rw [left.out_eq h x]
      exact hq
    obtain ⟨z, hz, rfl⟩ := hm
    exact ⟨z, rfl⟩
  · intro h p q hp hq
    obtain ⟨y, rfl⟩ := hp
    have hm : q ∈ right.toFun '' outY h y := by
      rw [right.out_eq h y]
      exact hq
    obtain ⟨z, hz, rfl⟩ := hm
    exact ⟨z, rfl⟩
  · exact pushout_covered ef.toFun eg.toFun
  · intro h
    obtain ⟨y, hy⟩ := hRightExtra
    have hz :
        (Sum.inr ⟨y, hy⟩ : PushoutCarrier ef.toFun eg.toFun) ∈
          Set.range left.toFun := by
      rw [h]
      exact Set.mem_univ _
    obtain ⟨x, hx⟩ := hz
    change (Sum.inl x : PushoutCarrier ef.toFun eg.toFun) =
      Sum.inr ⟨y, hy⟩ at hx
    cases hx
  · intro h
    obtain ⟨x, hx⟩ := hLeftExtra
    have hz : inclLeft ef.toFun eg.toFun x ∈
        Set.range right.toFun := by
      rw [h]
      exact Set.mem_univ _
    obtain ⟨y, hy⟩ := hz
    have eq : inclLeft ef.toFun eg.toFun x =
        inclRight ef.toFun eg.toFun y := hy.symm
    obtain ⟨i, hfi, _⟩ :=
      (left_eq_right_iff ef.toFun eg.toFun eg.injective x y).mp eq
    exact hx ⟨i, hfi.symm⟩
  · intro n r xs hrel
    change
      (∃ ys : Fin n → X,
        (fun i => inclLeft ef.toFun eg.toFun (ys i)) = xs ∧ RX.rel r ys) ∨
      (∃ zs : Fin n → Y,
        (fun i => inclRight ef.toFun eg.toFun (zs i)) = xs ∧ RY.rel r zs)
      at hrel
    rcases hrel with ⟨ys, eq, _⟩ | ⟨zs, eq, _⟩
    · left
      intro j
      exact ⟨ys j, congrFun eq j⟩
    · right
      intro j
      exact ⟨zs j, congrFun eq j⟩
  · intro h p hn
    have cover : p ∈ Set.range left.toFun ∪
        Set.range right.toFun := by
      change p ∈ Set.range (inclLeft ef.toFun eg.toFun) ∪
        Set.range (inclRight ef.toFun eg.toFun)
      rw [pushout_covered ef.toFun eg.toFun]
      exact Set.mem_univ p
    exact (hn cover).elim

end GluingEPPA.Sparsening.Tree
