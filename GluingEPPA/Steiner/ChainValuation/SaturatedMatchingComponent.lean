import GluingEPPA.Steiner.ChainValuation.ChainAttachReach

/-!
# A complete M-letter component cannot escape its Cayley block

The chain-restriction lemma has a separate first alternative: if an
occupied restricted block has alphabet exactly M, its M-component
does not grow when adjacent blocks are attached.

The mechanism is purely about partial matchings. If every M-letter
has a matching neighbour INSIDE a selected set W at each of its
vertices, uniqueness of matching neighbours prevents an M-edge from
leaving W. If W is M-connected, W is literally a full component.

We record the saturation criterion without invoking any hypothetical
full-stage group or commutativity. The actual chain extension also
preserves the saturation of an old subset through its injective
old-side map, using genuine union-of-block edges.

The remaining finite-history induction must apply these statements to
historical K_(M ∩ A) coset charts and their original source masks.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u} {X : Type v}

/-- Every M-letter at every selected vertex has its genuine matching
neighbour also inside W. This is stronger than mere closure of a
partially defined letter action and is the correct hypothesis for
the full K_M alternative of the normalization lemma. -/
def MatchingSaturated
    (P : E → Matching X) (M : Finset E) (W : Set X) : Prop :=
  ∀ (e : E), e ∈ M → ∀ x, x ∈ W →
    ∃ y, y ∈ W ∧ (P e).Rel x y

/-- Saturation and uniqueness of matching neighbours imply that
an M-path cannot cross the boundary of W in either direction. -/
theorem MatchingSaturated.reach_mem_iff
    (P : E → Matching X) (M : Finset E) (W : Set X)
    (hsat : MatchingSaturated P M W)
    {x y : X}
    (h : LabelReach (fun e => (P e).Rel) M x y) :
    x ∈ W ↔ y ∈ W := by
  have hEdge :
      ∀ (e : E), e ∈ M → ∀ ⦃a b : X⦄,
        (P e).Rel a b → (a ∈ W ↔ b ∈ W) := by
    intro e he a b hab
    constructor
    · intro ha
      obtain ⟨z, hz, haz⟩ := hsat e he a ha
      have hbz : b = z := (P e).unique hab haz
      rw [hbz]
      exact hz
    · intro hb
      obtain ⟨z, hz, hbz⟩ := hsat e he b hb
      have haz : a = z := (P e).unique ((P e).symm hab) hbz
      rw [haz]
      exact hz
  induction h with
  | refl x => exact Iff.rfl
  | edge e he hab => exact hEdge e he hab
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik

/-- If W is already connected by M-edges, saturation makes W
EXACTLY the full M-component of any one of its vertices.

In particular, a complete K_M-coset remains one whole component
when more blocks are attached; it cannot acquire additional
vertices through an M-edge without violating matching uniqueness. -/
theorem MatchingSaturated.component_iff
    (P : E → Matching X) (M : Finset E) (W : Set X)
    (hsat : MatchingSaturated P M W)
    (hconnected : ∀ x ∈ W, ∀ y ∈ W,
      LabelReach (fun e => (P e).Rel) M x y)
    (q : X) (hq : q ∈ W) (y : X) :
    LabelReach (fun e => (P e).Rel) M q y ↔ y ∈ W := by
  constructor
  · intro h
    exact (hsat.reach_mem_iff P M W h).mp hq
  · intro hy
    exact hconnected q hq y hy

/-- Genuine old matching edges remain genuine edges in a separated
chain extension. Hence saturation of an old subset survives the
actual Link-style injective pushout, with no extra pullback premise. -/
theorem extend_oldMatchingSaturated
    {K : Type v} [Group K]
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier)
    (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E) (W : Set C.Space)
    (hsat : MatchingSaturated C.matching M W) :
    MatchingSaturated
      (extend A B C h left right hl hr hsep hshared).matching M
      (oldEmbed A B C h left right hl hr '' W) := by
  intro e he x hx
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hab⟩ := hsat e he a ha
  refine ⟨oldEmbed A B C h left right hl hr b, ⟨b, hb, rfl⟩, ?_⟩
  exact Or.inl ⟨a, b, hab, rfl, rfl⟩

/-- An original full M-component which already saturates its
alphabet also remains the whole M-component of the extended
chain, via the injective old-block embedding. -/
theorem extend_oldSaturated_component_iff
    {K : Type v} [Group K]
    (A B : GroupBlock E) (C : ChainState E A)
    (h : A.Carrier)
    (left : K →* A.Carrier) (right : K →* B.Carrier)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hsep : Disjoint C.entry (exitSet A h left))
    (hshared : ∀ e, e ∈ A.active → e ∈ B.active →
      ∃ k : K, left k = A.edge e ∧ right k = B.edge e)
    (M : Finset E) (W : Set C.Space)
    (hsat : MatchingSaturated C.matching M W)
    (hconnected : ∀ x ∈ W, ∀ y ∈ W,
      LabelReach (fun e => (C.matching e).Rel) M x y)
    (q : C.Space) (hq : q ∈ W)
    (v : (extend A B C h left right hl hr hsep hshared).Space) :
    LabelReach
      (fun e => ((extend A B C h left right hl hr hsep hshared).matching e).Rel)
      M (oldEmbed A B C h left right hl hr q) v ↔
      v ∈ oldEmbed A B C h left right hl hr '' W := by
  let F := oldEmbed A B C h left right hl hr
  have hs : MatchingSaturated
      (extend A B C h left right hl hr hsep hshared).matching M
      (F '' W) :=
    extend_oldMatchingSaturated A B C h left right hl hr
      hsep hshared M W hsat
  have hc : ∀ x ∈ F '' W, ∀ y ∈ F '' W,
      LabelReach
        (fun e =>
          ((extend A B C h left right hl hr hsep hshared).matching e).Rel)
        M x y := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact LabelReach.map
      (fun e => (C.matching e).Rel)
      (fun e =>
        ((extend A B C h left right hl hr hsep hshared).matching e).Rel)
      M F
      (fun e p r hpr => Or.inl ⟨p, r, hpr, rfl, rfl⟩)
      (hconnected a ha b hb)
  exact hs.component_iff _ M (F '' W) hc (F q) ⟨q, hq, rfl⟩ v

end GluingEPPA.Steiner.ChainValuation
