import GluingEPPA.Sparsening.TreeFreeCutHom

/-!
# Strong-amalgam relations and set-valued unary functions

The candidate structure is the union of the two exact source structures,
interpreted on the genuine pushout carrier. Its relation tuples and unary
fibres are contributed by a source side containing the whole input tuple.

This ports the semantic constructors from the already verified
AllThoseEPPA/TreeLikeAmalgamStructure.lean, without the separate nontrivial
language-symbol action. Source maps are proved to be homomorphisms here;
exact reflection and full unary equality will be proved next.
-/
namespace GluingEPPA.Sparsening.Tree
universe u v w x t
variable {L : Nat → Type u} {F : Type t}
variable {I : Type v} {X : Type w} {Y : Type x}

/-- Exact embeddings have the same full-fibre function equation as the
public AllThoseEPPA.Structure.Embedding, restricted to trivial actions. -/
structure ExactUnaryEmbedding
    (RI : RelStructure L I) (outI : F → I → Set I)
    (RX : RelStructure L X) (outX : F → X → Set X) where
  toFun : I → X
  injective : Function.Injective toFun
  rel_iff : ∀ {n} (r : L n) (xs : Fin n → I),
    RX.rel r (fun i => toFun (xs i)) ↔ RI.rel r xs
  out_eq : ∀ f i, toFun '' outI f i = outX f (toFun i)

/-- Tuples are present iff contributed in full by one side; zero-ary and
repeated-coordinate relations are included without exceptional cases. -/
noncomputable def pushoutRelations
    (f : I → X) (g : I → Y)
    (RX : RelStructure L X) (RY : RelStructure L Y) :
    RelStructure L (PushoutCarrier f g) where
  rel := by
    intro n r zs
    exact
      (∃ xs : Fin n → X,
        (fun i => inclLeft f g (xs i)) = zs ∧ RX.rel r xs) ∨
      (∃ ys : Fin n → Y,
        (fun i => inclRight f g (ys i)) = zs ∧ RY.rel r ys)

/-- Unary fibres consist precisely of the union of represented source
fibres, with no additional mixed-side output. -/
noncomputable def pushoutOutput
    (f : I → X) (g : I → Y)
    (outX : F → X → Set X) (outY : F → Y → Set Y) :
    F → PushoutCarrier f g → Set (PushoutCarrier f g) :=
  fun h z =>
    {w | (∃ x : X, inclLeft f g x = z ∧
        w ∈ inclLeft f g '' outX h x) ∨
      (∃ y : Y, inclRight f g y = z ∧
        w ∈ inclRight f g '' outY h y)}

/-- First side maps homomorphically to the candidate free amalgam. -/
theorem left_map_rel (f : I → X) (g : I → Y)
    (RX : RelStructure L X) (RY : RelStructure L Y)
    {n} (r : L n) (xs : Fin n → X) (hr : RX.rel r xs) :
    (pushoutRelations f g RX RY).rel r
      (fun i => inclLeft f g (xs i)) := by
  exact Or.inl ⟨xs, rfl, hr⟩

theorem right_map_rel (f : I → X) (g : I → Y)
    (RX : RelStructure L X) (RY : RelStructure L Y)
    {n} (r : L n) (ys : Fin n → Y) (hr : RY.rel r ys) :
    (pushoutRelations f g RX RY).rel r
      (fun i => inclRight f g (ys i)) := by
  exact Or.inr ⟨ys, rfl, hr⟩

/-- Left unary map preserves every member of the whole output fibre. -/
theorem left_map_unary (f : I → X) (g : I → Y)
    (outX : F → X → Set X) (outY : F → Y → Set Y)
    (h : F) (x z : X) (hz : z ∈ outX h x) :
    inclLeft f g z ∈
      pushoutOutput f g outX outY h (inclLeft f g x) := by
  exact Or.inl ⟨x, rfl, z, hz, rfl⟩

/-- Right unary map, including points glued to the left interface. -/
theorem right_map_unary (f : I → X) (g : I → Y)
    (outX : F → X → Set X) (outY : F → Y → Set Y)
    (h : F) (y z : Y) (hz : z ∈ outY h y) :
    inclRight f g z ∈
      pushoutOutput f g outX outY h (inclRight f g y) := by
  exact Or.inr ⟨y, rfl, z, hz, rfl⟩

end GluingEPPA.Sparsening.Tree
