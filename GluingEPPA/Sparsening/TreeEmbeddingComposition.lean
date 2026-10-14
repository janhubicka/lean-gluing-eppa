import GluingEPPA.Sparsening.TreeStrongAmalgam

/-!
# Exact unary embeddings compose

Port of the small reusable maps interface used by
AllThoseEPPA/TreeLikeFullAAmalgamation. A source copy may first embed into
a larger tree component, and the gluing root may be embedded inside this copy.
Full unary-fibre equality, rather than bare preservation, makes this
composition strict and keeps the interface closed.
-/
namespace GluingEPPA.Sparsening.Tree
universe u v w x t
variable {L : Nat → Type u} {F : Type t}
variable {A : Type v} {B : Type w} {C : Type x}

namespace ExactUnaryEmbedding

/-- Exact embeddings compose, including all relation symbols and whole
unary output fibres. -/
def comp
    {RA : RelStructure L A} {RB : RelStructure L B} {RC : RelStructure L C}
    {outA : F → A → Set A} {outB : F → B → Set B}
    {outC : F → C → Set C}
    (g : ExactUnaryEmbedding RB outB RC outC)
    (f : ExactUnaryEmbedding RA outA RB outB) :
    ExactUnaryEmbedding RA outA RC outC where
  toFun := fun x => g.toFun (f.toFun x)
  injective := by
    intro x y h
    exact f.injective (g.injective h)
  rel_iff := by
    intro n r xs
    exact (g.rel_iff r (fun i => f.toFun (xs i))).trans (f.rel_iff r xs)
  out_eq := by
    intro h x
    have hcomp :
        (fun a => g.toFun (f.toFun a)) '' outA h x =
          g.toFun '' (f.toFun '' outA h x) := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨f.toFun a, ⟨a, ha, rfl⟩, rfl⟩
      · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
    calc
      (fun a => g.toFun (f.toFun a)) '' outA h x =
        g.toFun '' (f.toFun '' outA h x) := hcomp
      _ = g.toFun '' outB h (f.toFun x) :=
        congrArg (fun s : Set B => g.toFun '' s) (f.out_eq h x)
      _ = outC h (g.toFun (f.toFun x)) := g.out_eq h (f.toFun x)

/-- Exact unary fibre preservation forces the embedding image to be closed.
The target may have arbitrary branching, cyclic or empty unary fibres. -/
theorem range_closed
    {RA : RelStructure L A} {RB : RelStructure L B}
    {outA : F → A → Set A} {outB : F → B → Set B}
    (e : ExactUnaryEmbedding RA outA RB outB) :
    UnaryClosed outB (fun y => y ∈ Set.range e.toFun) := by
  intro h x y hx hy
  obtain ⟨a, rfl⟩ := hx
  have hm : y ∈ e.toFun '' outA h a := by
    rw [e.out_eq h a]
    exact hy
  obtain ⟨b, hb, rfl⟩ := hm
  exact ⟨b, rfl⟩

/-- Any relation witnessed on a source-image tuple reflects uniquely
to the original source, also in the presence of nullary symbols. -/
theorem map_rel_iff
    {RA : RelStructure L A} {RB : RelStructure L B}
    {outA : F → A → Set A} {outB : F → B → Set B}
    (e : ExactUnaryEmbedding RA outA RB outB)
    {n : Nat} (r : L n) (xs : Fin n → A) :
    RB.rel r (fun i => e.toFun (xs i)) ↔ RA.rel r xs :=
  e.rel_iff r xs

end ExactUnaryEmbedding
end GluingEPPA.Sparsening.Tree
