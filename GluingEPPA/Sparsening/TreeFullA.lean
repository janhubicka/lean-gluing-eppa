import GluingEPPA.Sparsening.TreeEmbeddingComposition

/-!
# Literal recursive tree amalgamations of full copies of A

This is a precise unary-language specialization of the certified
AllThoseEPPA/TreeLikeFullAAmalgamation.lean constructor.
The leaf is a genuine *full* copy of A. Every gluing interface embeds into
the distinguished A-copy of BOTH target branches; thus a mere arbitrary
free decomposition does not count as a legal A-tree attachment.

We reuse the exact strong-pushout relation and unary interpretations and
the fully verified composition of exact embeddings. Nothing here assumes
the local-tree sparsening conclusion.
-/
namespace GluingEPPA.Sparsening.Tree
universe u v t
variable {L : Nat → Type u} {F : Type t} {A : Type v}

/-- Identity embeds all unary fibres and relations exactly. -/
def ExactUnaryEmbedding.refl (RA : RelStructure L A)
    (outA : F → A → Set A) :
    ExactUnaryEmbedding RA outA RA outA where
  toFun := id
  injective := by intro x y h; exact h
  rel_iff := by intro n r xs; exact Iff.rfl
  out_eq := by
    intro f x
    change id '' outA f x = outA f x
    simp

/-- Recursive trees built only from full copies of A and free
amalgamations over interfaces lying inside full A-copies on both sides. -/
inductive FullATree
    (RA : RelStructure L A) (outA : F → A → Set A) :
    {V : Type v} → RelStructure L V → (F → V → Set V) → Prop where
  | copy {V : Type v}
      (RV : RelStructure L V) (outV : F → V → Set V)
      (e : ExactUnaryEmbedding RA outA RV outV)
      (surjective : Function.Surjective e.toFun) :
      FullATree RA outA RV outV
  | glue {I X Y : Type v}
      (RI : RelStructure L I) (outI : F → I → Set I)
      (RX : RelStructure L X) (outX : F → X → Set X)
      (RY : RelStructure L Y) (outY : F → Y → Set Y)
      (hX : FullATree RA outA RX outX)
      (hY : FullATree RA outA RY outY)
      (δX δY : ExactUnaryEmbedding RI outI RA outA)
      (αX : ExactUnaryEmbedding RA outA RX outX)
      (αY : ExactUnaryEmbedding RA outA RY outY) :
      FullATree RA outA
        (pushoutRelations (αX.comp δX).toFun (αY.comp δY).toFun RX RY)
        (pushoutOutput (αX.comp δX).toFun (αY.comp δY).toFun outX outY)

/-- The one-node full A-tree. -/
theorem FullATree.singleton (RA : RelStructure L A)
    (outA : F → A → Set A) :
    FullATree RA outA RA outA :=
  .copy RA outA (ExactUnaryEmbedding.refl RA outA)
    (fun a => ⟨a, rfl⟩)

/-- Every tree built by this strict constructor contains a full
embedded copy of A. A free-amalgam gluing retains the left copy exactly. -/
theorem FullATree.contains_A
    (RA : RelStructure L A) (outA : F → A → Set A)
    {V : Type v} (RV : RelStructure L V) (outV : F → V → Set V)
    (h : FullATree RA outA RV outV) :
    Nonempty (ExactUnaryEmbedding RA outA RV outV) := by
  induction h with
  | copy RV outV e surjective =>
    exact ⟨e⟩
  | glue RI outI RX outX RY outY hX hY δX δY αX αY ihX ihY =>
    let f := αX.comp δX
    let g := αY.comp δY
    exact ⟨(leftExactEmbedding RI outI RX outX RY outY f g).comp αX⟩

/-- Every literal strict tree of full A-copies has a finite carrier when
the original A is finite. No separate bound or finiteness hypothesis on
the intermediate gluing interfaces is needed. -/
theorem FullATree.carrier_finite
    (RA : RelStructure L A) (outA : F → A → Set A)
    [Finite A]
    {V : Type v} (RV : RelStructure L V) (outV : F → V → Set V)
    (tree : FullATree RA outA RV outV) :
    Finite V := by
  induction tree with
  | copy RV outV e surjective =>
      exact Finite.of_surjective e.toFun surjective
  | glue RI outI RX outX RY outY hX hY δX δY αX αY ihX ihY =>
      letI : Finite _ := ihX
      letI : Finite _ := ihY
      exact pushout_finite
        (αX.comp δX).toFun (αY.comp δY).toFun


end GluingEPPA.Sparsening.Tree
