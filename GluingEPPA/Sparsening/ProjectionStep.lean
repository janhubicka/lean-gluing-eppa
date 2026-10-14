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


/-- Direct set/subtype cardinality form of the proper-piece image bound.
If a finite source side is proper, its image cannot have k+1 points
when the entire source has at most k+1 points. No injectivity
hypothesis and no quotient structure is needed. This is the numerical
induction lemma for genuine upstairs free cuts. -/
theorem proper_set_image_small [Finite P] [Finite B]
    (p : P → B) (Y : Set P) (hproper : Y ≠ Set.univ)
    (k : Nat) (hcard : Nat.card P ≤ k + 1) :
    Nat.card (p '' Y) ≤ k := by
  classical
  letI : Fintype P := Fintype.ofFinite _
  letI : Fintype Y := Fintype.ofFinite _
  letI : Fintype (p '' Y) := Fintype.ofFinite _
  have hcard' : Fintype.card P ≤ k + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hnot : ¬ Function.Surjective (fun z : Y => z.val) := by
    intro hs
    apply hproper
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨y, hy⟩ := hs z
    exact hy ▸ y.property
  have hlt : Fintype.card Y < Fintype.card P :=
    Fintype.card_lt_of_injective_not_surjective
      (fun z : Y => z.val) Subtype.val_injective hnot
  have hsurj : Function.Surjective
      (fun z : Y => (⟨p z.val, ⟨z.val, z.property, rfl⟩⟩ : p '' Y)) := by
    rintro ⟨b, ⟨z, hz, heq⟩⟩
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    exact heq
  have hle : Fintype.card (p '' Y) ≤ Fintype.card Y :=
    Fintype.card_le_of_surjective _ hsurj
  have hgoal : Fintype.card (p '' Y) ≤ k := by omega
  simpa only [Nat.card_eq_fintype_card] using hgoal

end GluingEPPA.Sparsening
