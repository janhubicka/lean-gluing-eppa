import GluingEPPA.Sparsening.ClosedCuts

/-!
Set-theoretic interfaces in the local-tree induction. The noninjective
case decreases image size. Only in the injective case may the projected
root be identified with the intersection of the two projected pieces.
-/
namespace GluingEPPA.Sparsening
universe u v w
variable {P : Type u} {B : Type v} {F : Type w}

/-- This is the size split used at stage k+1; no cycle-length claim occurs. -/
theorem image_small_or_injective [DecidableEq B]
    (p : P → B) (X : Finset P) (k : Nat) (size : X.card ≤ k + 1) :
    (X.image p).card ≤ k ∨ Set.InjOn p X := by
  by_cases small : (X.image p).card ≤ k
  · exact Or.inl small
  · right
    have hle : (X.image p).card ≤ X.card := Finset.card_image_le
    have heq : (X.image p).card = X.card := by omega
    exact Finset.injOn_of_card_image_eq heq

/-- Each proper separator piece is small enough for the previous stage. -/
theorem proper_piece_image_small [DecidableEq B]
    (p : P → B) (Y X : Finset P) (k : Nat)
    (proper : Y ⊂ X) (size : X.card ≤ k + 1) : (Y.image p).card ≤ k := by
  have hlt : Y.card < X.card := Finset.card_lt_card proper
  have hle : (Y.image p).card ≤ Y.card := Finset.card_image_le
  omega

/-- The old induced root is exactly the intersection of the old pieces
when the projection is injective on their union. -/
theorem image_inter_of_injective_union (p : P → B) (X Y : Set P)
    (inj : Set.InjOn p (X ∪ Y)) :
    p '' (X ∩ Y) = (p '' X) ∩ (p '' Y) := by
  ext b
  constructor
  · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hy, rfl⟩⟩
  · rintro ⟨⟨x, hx, hxb⟩, ⟨y, hy, hyb⟩⟩
    have hxy : x = y := inj (Or.inl hx) (Or.inr hy) (hxb.trans hyb.symm)
    exact ⟨x, ⟨hx, hxy.symm ▸ hy⟩, hxb⟩

/-- Equality of complete unary fibres makes projected closed tests closed.
Preservation of graph pairs alone would not justify this lemma. -/
theorem unary_image_closed
    (out : F → P → Set P) (outB : F → B → Set B)
    (C : P → Prop) (closed : UnaryClosed out C) (p : P → B)
    (fibres : ∀ f x, p '' (out f x) = outB f (p x)) :
    UnaryClosed outB (fun b => ∃ x, C x ∧ p x = b) := by
  rintro f b c ⟨x, hx, rfl⟩ hc
  rw [← fibres f x] at hc
  obtain ⟨y, hy, rfl⟩ := hc
  exact ⟨y, closed f x y hx hy, rfl⟩

end GluingEPPA.Sparsening
