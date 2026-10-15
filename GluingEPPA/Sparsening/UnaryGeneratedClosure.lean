import GluingEPPA.Sparsening.TreeHomEmbedding

/-!
# One-generated closure and complete unary fibres

A closed side of a free decomposition containing the generator contains
its whole closure. Therefore a one-generated closed structure is
irreducible, independently of the relations. Exactness on these tests
forces every UnaryHomEmbedding to preserve equality of entire unary
fibres. This identifies the internal record with the manuscript's
homomorphism convention; forward preservation alone would not suffice.
-/

namespace GluingEPPA.Sparsening

universe u v w t
variable {L : Nat → Type u} {A : Type v} {B : Type w} {F : Type t}

/-- The least set closed under all unary outputs and containing a. -/
def unaryClosure (out : F → A → Set A) (a : A) : Set A :=
  {b | ∀ S : Set A, UnaryClosed out (fun x => x ∈ S) → a ∈ S → b ∈ S}

theorem mem_unaryClosure (out : F → A → Set A) (a : A) :
    a ∈ unaryClosure out a := by
  intro S hS ha
  exact ha

theorem unaryClosure_closed (out : F → A → Set A) (a : A) :
    UnaryClosed out (fun x => x ∈ unaryClosure out a) := by
  intro f x y hx hy S hS ha
  exact hS f x y (hx S hS ha) hy

theorem unaryClosure_minimal (out : F → A → Set A) (a : A)
    (S : Set A) (hS : UnaryClosed out (fun x => x ∈ S)) (ha : a ∈ S) :
    unaryClosure out a ⊆ S := by
  intro b hb
  exact hb S hS ha

/-- Any closed subset of the generated structure containing its generator
is the whole structure. Unary fibres may be empty, branching or cyclic. -/
theorem unaryClosure_closed_subset_eq_univ (out : F → A → Set A) (a : A)
    (D : Set (unaryClosure out a))
    (hD : UnaryClosed (inducedUnary out (unaryClosure out a))
      (fun x => x ∈ D))
    (ha : (⟨a, mem_unaryClosure out a⟩ : unaryClosure out a) ∈ D) :
    D = Set.univ := by
  have hc : UnaryClosed out
      (fun x => x ∈ (Subtype.val '' D : Set A)) :=
    unary_image_closed (inducedUnary out (unaryClosure out a)) out
      (fun x => x ∈ D) hD Subtype.val
      (inducedUnary_full out (unaryClosure out a) (unaryClosure_closed out a))
  have hsub : unaryClosure out a ⊆ (Subtype.val '' D : Set A) :=
    unaryClosure_minimal out a _ hc
      ⟨⟨a, mem_unaryClosure out a⟩, ha, rfl⟩
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨y, hy, heq⟩ := hsub z.property
  exact (Subtype.ext heq : y = z) ▸ hy

/-- A single generator cannot lie on a proper closed side of a free cut. -/
theorem unaryClosure_irreducible (R : RelStructure L A)
    (out : F → A → Set A) (a : A) :
    IsIrreducible (inducedRelations R (unaryClosure out a))
      (inducedUnary out (unaryClosure out a)) := by
  constructor
  intro d
  let z : unaryClosure out a := ⟨a, mem_unaryClosure out a⟩
  have hz : z ∈ d.left ∪ d.right := by
    rw [d.cover]
    exact Set.mem_univ z
  rcases hz with hl | hr
  · exact d.left_proper
      (unaryClosure_closed_subset_eq_univ out a d.left d.left_closed hl)
  · exact d.right_proper
      (unaryClosure_closed_subset_eq_univ out a d.right d.right_closed hr)

namespace Tree.UnaryHomEmbedding

variable {RA : RelStructure L A} {RB : RelStructure L B}
variable {outA : F → A → Set A} {outB : F → B → Set B}

/-- The internal exact-on-irreducibles record preserves complete fibres,
not just forward membership. No finiteness hypothesis is necessary. -/
theorem out_eq (h : UnaryHomEmbedding RA outA RB outB) (f : F) (a : A) :
    h.toFun '' outA f a = outB f (h.toFun a) := by
  obtain ⟨e, he⟩ := h.exact_on_irred (unaryClosure outA a)
    (unaryClosure_closed outA a) (unaryClosure_irreducible RA outA a)
  let z : unaryClosure outA a := ⟨a, mem_unaryClosure outA a⟩
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact h.unary_map f a x hx
  · intro hb
    have hb' : b ∈ outB f (e.toFun z) := by
      rw [he z]
      exact hb
    rw [← e.out_eq f z] at hb'
    obtain ⟨x, hx, hxb⟩ := hb'
    exact ⟨x.val, hx, (he x).symm.trans hxb⟩

/-- The image of any closed source subset under a homomorphism-embedding
is closed, even when the map identifies vertices. -/
theorem image_closed (h : UnaryHomEmbedding RA outA RB outB)
    (S : Set A) (hS : UnaryClosed outA (fun x => x ∈ S)) :
    UnaryClosed outB (fun y => y ∈ h.toFun '' S) :=
  unary_image_closed outA outB (fun x => x ∈ S) hS h.toFun h.out_eq

end Tree.UnaryHomEmbedding
end GluingEPPA.Sparsening
