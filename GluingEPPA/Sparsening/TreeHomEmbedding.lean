import GluingEPPA.Sparsening.TreeFreeCutPushoutHom

/-!
# Composition of unary relational homomorphism-embeddings

An exact embedding has a closed induced range, and an irreducible source
has an irreducible induced range. The latter is proved by pulling any
hypothetical free decomposition back along the exact embedding.

A homomorphism-embedding need only be exact on irreducible closed tests,
not globally injective. The exact image of such a test is another
irreducible closed test, allowing two homomorphism-embeddings to compose.
-/
namespace GluingEPPA.Sparsening.Tree

universe u v w x t
variable {L : Nat → Type u} {F : Type t}
variable {A : Type v} {B : Type w} {C : Type x}

namespace ExactUnaryEmbedding

/-- Every exact embedding factors exactly through its closed induced range. -/
def toClosedRange
    {RA : RelStructure L A} {RB : RelStructure L B}
    {outA : F → A → Set A} {outB : F → B → Set B}
    (e : ExactUnaryEmbedding RA outA RB outB) :
    ExactUnaryEmbedding RA outA
      (inducedRelations RB (Set.range e.toFun))
      (inducedUnary outB (Set.range e.toFun)) where
  toFun := fun a => ⟨e.toFun a, ⟨a, rfl⟩⟩
  injective := by
    intro a b hab
    exact e.injective (congrArg Subtype.val hab)
  rel_iff := by
    intro n r xs
    exact e.rel_iff r xs
  out_eq := by
    intro f a
    ext b
    constructor
    · rintro ⟨z, hz, rfl⟩
      change e.toFun z ∈ outB f (e.toFun a)
      rw [← e.out_eq f a]
      exact ⟨z, hz, rfl⟩
    · intro hb
      have hh : b.val ∈ outB f (e.toFun a) := hb
      rw [← e.out_eq f a] at hh
      obtain ⟨z, hz, hzb⟩ := hh
      refine ⟨z, hz, ?_⟩
      exact Subtype.ext hzb

/-- Exact unary/relational embeddings transport irreducibility to their
closed induced image; this includes empty source and nullary relations. -/
theorem range_irreducible
    {RA : RelStructure L A} {RB : RelStructure L B}
    {outA : F → A → Set A} {outB : F → B → Set B}
    (e : ExactUnaryEmbedding RA outA RB outB)
    (hirr : IsIrreducible RA outA) :
    IsIrreducible (inducedRelations RB (Set.range e.toFun))
      (inducedUnary outB (Set.range e.toFun)) := by
  classical
  let j : A → Set.range e.toFun := fun a => ⟨e.toFun a, ⟨a, rfl⟩⟩
  constructor
  intro d
  let cut : UnaryFreeDecomposition RA outA :=
    { left := {a | j a ∈ d.left}
      right := {a | j a ∈ d.right}
      left_closed := by
        intro f a b ha hb
        apply d.left_closed f (j a) (j b) ha
        change e.toFun b ∈ outB f (e.toFun a)
        rw [← e.out_eq f a]
        exact ⟨b, hb, rfl⟩
      right_closed := by
        intro f a b ha hb
        apply d.right_closed f (j a) (j b) ha
        change e.toFun b ∈ outB f (e.toFun a)
        rw [← e.out_eq f a]
        exact ⟨b, hb, rfl⟩
      cover := by
        apply Set.eq_univ_of_forall
        intro a
        have ha : j a ∈ d.left ∪ d.right := by
          rw [d.cover]
          exact Set.mem_univ (j a)
        exact ha
      left_proper := by
        intro hall
        apply d.left_proper
        apply Set.eq_univ_of_forall
        rintro ⟨b, hb⟩
        obtain ⟨a, ha⟩ := hb
        have hbrange : b ∈ Set.range e.toFun := ⟨a, ha⟩
        have he : j a = (⟨b, hbrange⟩ : Set.range e.toFun) :=
          Subtype.ext ha
        rw [← he]
        have haa : a ∈ ({a | j a ∈ d.left} : Set A) := by
          rw [hall]
          exact Set.mem_univ a
        exact haa
      right_proper := by
        intro hall
        apply d.right_proper
        apply Set.eq_univ_of_forall
        rintro ⟨b, hb⟩
        obtain ⟨a, ha⟩ := hb
        have hbrange : b ∈ Set.range e.toFun := ⟨a, ha⟩
        have he : j a = (⟨b, hbrange⟩ : Set.range e.toFun) :=
          Subtype.ext ha
        rw [← he]
        have haa : a ∈ ({a | j a ∈ d.right} : Set A) := by
          rw [hall]
          exact Set.mem_univ a
        exact haa
      rel_local := by
        intro n r xs hr
        have hb : (inducedRelations RB (Set.range e.toFun)).rel r
            (fun i => j (xs i)) := by
          change RB.rel r (fun i => e.toFun (xs i))
          exact (e.rel_iff r xs).mpr hr
        rcases d.rel_local r (fun i => j (xs i)) hb with hl | hr
        · exact Or.inl hl
        · exact Or.inr hr
      func_cross_empty := by
        intro f a hn
        have hm : j a ∈ d.left ∪ d.right := by
          rw [d.cover]
          exact Set.mem_univ (j a)
        exact (hn hm).elim }
  exact hirr.false cut

end ExactUnaryEmbedding

/-- Homomorphisms that are exact on all closed irreducible tests, including
full unary fibres. No global injectivity is required. -/
structure UnaryHomEmbedding
    (RA : RelStructure L A) (outA : F → A → Set A)
    (RB : RelStructure L B) (outB : F → B → Set B) where
  toFun : A → B
  rel_map : ∀ {n} (r : L n) (xs : Fin n → A),
    RA.rel r xs → RB.rel r (fun i => toFun (xs i))
  unary_map : ∀ f a b, b ∈ outA f a → toFun b ∈ outB f (toFun a)
  exact_on_irred : ∀ (S : Set A),
    UnaryClosed outA (fun a => a ∈ S) →
    IsIrreducible (inducedRelations RA S) (inducedUnary outA S) →
    ∃ e : ExactUnaryEmbedding
        (inducedRelations RA S) (inducedUnary outA S) RB outB,
      ∀ z : S, e.toFun z = toFun z.val

namespace UnaryHomEmbedding

/-- Homomorphism-embeddings compose because the first map sends every
irreducible closed test onto a closed irreducible induced image. -/
def comp
    {RA : RelStructure L A} {RB : RelStructure L B}
    {RC : RelStructure L C}
    {outA : F → A → Set A} {outB : F → B → Set B}
    {outC : F → C → Set C}
    (g : UnaryHomEmbedding RB outB RC outC)
    (f : UnaryHomEmbedding RA outA RB outB) :
    UnaryHomEmbedding RA outA RC outC where
  toFun := fun a => g.toFun (f.toFun a)
  rel_map := by
    intro n r xs hr
    exact g.rel_map r (fun i => f.toFun (xs i)) (f.rel_map r xs hr)
  unary_map := by
    intro h a b hab
    exact g.unary_map h (f.toFun a) (f.toFun b)
      (f.unary_map h a b hab)
  exact_on_irred := by
    intro S hclosed hirr
    obtain ⟨e, he⟩ := f.exact_on_irred S hclosed hirr
    let T : Set B := Set.range e.toFun
    have hclosedT : UnaryClosed outB (fun b => b ∈ T) :=
      e.range_closed
    have hirrT : IsIrreducible
        (inducedRelations RB T) (inducedUnary outB T) :=
      e.range_irreducible hirr
    obtain ⟨e2, he2⟩ := g.exact_on_irred T hclosedT hirrT
    refine ⟨e2.comp e.toClosedRange, ?_⟩
    intro a
    change e2.toFun (⟨e.toFun a, ⟨a, rfl⟩⟩ : T) =
      g.toFun (f.toFun a.val)
    calc
      e2.toFun (⟨e.toFun a, ⟨a, rfl⟩⟩ : T) =
          g.toFun (e.toFun a) := he2 ⟨e.toFun a, ⟨a, rfl⟩⟩
      _ = g.toFun (f.toFun a.val) := congrArg g.toFun (he a)

end UnaryHomEmbedding
end GluingEPPA.Sparsening.Tree
