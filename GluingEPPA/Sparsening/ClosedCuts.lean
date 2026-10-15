import GluingEPPA.Sparsening.StarCorrection
import GluingEPPA.Relational

/-!
A concrete free-amalgam certificate for the exterior-coordinate separator.
Unary outputs may be arbitrary sets. Relation tuples have arbitrary arity,
including zero, and may have repeated entries. This module does not assert
that an unspecified quotient has the required local record properties.
-/
namespace GluingEPPA.Sparsening
universe u v w z t
variable {P : Type w} {F : Type z} {L : Nat → Type t}

/-- Closure under every value of each unary set-valued function. -/
def UnaryClosed (out : F → P → Set P) (C : P → Prop) : Prop :=
  ∀ f x y, C x → y ∈ out f x → C y

/-- The restrictions to the two sides freely amalgamate to the whole carrier.
Closedness handles full function fibres, rather than only graph homomorphisms. -/
structure ClosedCut (R : RelStructure L P) (out : F → P → Set P)
    (root : P → Prop) where
  left : P → Prop
  right : P → Prop
  cover : ∀ p, left p ∨ right p
  intersection : ∀ p, (left p ∧ right p) ↔ root p
  proper_left : ∃ p, ¬ left p
  proper_right : ∃ p, ¬ right p
  left_closed : UnaryClosed out left
  right_closed : UnaryClosed out right
  root_closed : UnaryClosed out root
  tuple_side : ∀ {n} (r : L n) (x : Fin n → P), R.rel r x →
    (∀ i, left (x i)) ∨ (∀ i, right (x i))

lemma bit_two_values (a b x : ZMod 2) (h : a ≠ b) : x = a ∨ x = b :=
  (by decide : ∀ a b x : ZMod 2, a ≠ b → x = a ∨ x = b) a b x h

def cutSide (root : P → Prop) (bit : P → ZMod 2) (b : ZMod 2) (p : P) : Prop :=
  root p ∨ bit p = b

lemma cutSide_closed (out : F → P → Set P) (root : P → Prop)
    (bit : P → ZMod 2) (root_closed : UnaryClosed out root)
    (same : ∀ f x y, y ∈ out f x → ¬ root x → ¬ root y → bit x = bit y)
    (b : ZMod 2) : UnaryClosed out (cutSide root bit b) := by
  classical
  intro f x y hx hy
  by_cases hrx : root x
  · exact Or.inl (root_closed f x y hrx hy)
  · by_cases hry : root y
    · exact Or.inl hry
    · have hb : bit x = b := hx.resolve_left hrx
      exact Or.inr ((same f x y hy hrx hry).symm.trans hb)

lemma tuple_cutSide {n : Nat} (root : P → Prop) (bit : P → ZMod 2)
    (a b : ZMod 2) (hab : a ≠ b) (x : Fin n → P)
    (same : ∀ i j, ¬ root (x i) → ¬ root (x j) → bit (x i) = bit (x j)) :
    (∀ i, cutSide root bit a (x i)) ∨ (∀ i, cutSide root bit b (x i)) := by
  classical
  by_cases he : ∃ i, ¬ root (x i)
  · obtain ⟨i, hi⟩ := he
    rcases bit_two_values a b (bit (x i)) hab with ha | hb
    · left
      intro j
      by_cases hj : root (x j)
      · exact Or.inl hj
      · exact Or.inr ((same i j hi hj).symm.trans ha)
    · right
      intro j
      by_cases hj : root (x j)
      · exact Or.inl hj
      · exact Or.inr ((same i j hi hj).symm.trans hb)
  · left
    intro i
    apply Or.inl
    by_contra hi
    exact he ⟨i, hi⟩

/-- Different defined exterior values give a proper closed decomposition. -/
noncomputable def closedCut_of_disagreement
    (R : RelStructure L P) (out : F → P → Set P)
    (root : P → Prop) (bit : P → ZMod 2)
    (root_closed : UnaryClosed out root)
    (unary_same : ∀ f x y, y ∈ out f x → ¬ root x → ¬ root y → bit x = bit y)
    (relation_same : ∀ {n} (r : L n) (x : Fin n → P), R.rel r x →
      ∀ i j, ¬ root (x i) → ¬ root (x j) → bit (x i) = bit (x j))
    (p q : P) (hp : ¬ root p) (hq : ¬ root q) (hd : bit p ≠ bit q) :
    ClosedCut R out root where
  left := cutSide root bit (bit p)
  right := cutSide root bit (bit q)
  cover x := by
    rcases bit_two_values (bit p) (bit q) (bit x) hd with ha | hb
    · exact Or.inl (Or.inr ha)
    · exact Or.inr (Or.inr hb)
  intersection x := by
    constructor
    · rintro ⟨hx, hy⟩
      rcases hx with hr | ha
      · exact hr
      · rcases hy with hr | hb
        · exact hr
        · exact False.elim (hd (ha.symm.trans hb))
    · intro hr
      exact ⟨Or.inl hr, Or.inl hr⟩
  proper_left := ⟨q, fun h => h.elim hq (fun h => hd h.symm)⟩
  proper_right := ⟨p, fun h => h.elim hp hd⟩
  left_closed := cutSide_closed out root bit root_closed unary_same (bit p)
  right_closed := cutSide_closed out root bit root_closed unary_same (bit q)
  root_closed := root_closed
  tuple_side r x hx := tuple_cutSide root bit (bit p) (bit q) hd x
    (relation_same r x hx)

variable {V : Type u} {E : Type v}
variable (G : GluingEPPA.EdgeGraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The record-level chart-or-closed-separator dichotomy. The remaining
geometric interface is to prove that record equality is exactly quotient
equality and that the concrete quotient supplies the local hypotheses. -/
theorem record_chart_or_closed_cut
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (support : P → V → Prop) (origin : P → V)
    (chi : P → E → ZMod 2) (alpha : V → ZMod 2)
    (origin_mem : ∀ p, support p (origin p))
    (odd : (∑ v, alpha v) = 1)
    (record : ∀ p v,
      boundary G (chi p) v + (if origin p = v then 1 else 0) = alpha v)
    (R : RelStructure L P) (out : F → P → Set P)
    (support_mono : ∀ f x y, y ∈ out f x → ∀ v, support x v → support y v)
    (unary_same : ∀ f x y, y ∈ out f x → ∀ e,
      ¬ internal G support x e → ¬ internal G support y e → chi x e = chi y e)
    (relation_same : ∀ {n} (r : L n) (x : Fin n → P), R.rel r x →
      ∀ i j e, ¬ internal G support (x i) e → ¬ internal G support (x j) e →
        chi (x i) e = chi (x j) e) :
    (∃ s c, (∀ p, support p s) ∧
      (∀ p e, ¬ internal G support p e → c e = chi p e) ∧
      (∀ v, boundary G c v + (if s = v then 1 else 0) = alpha v)) ∨
    (∃ e, Nonempty (ClosedCut R out (fun p => internal G support p e))) := by
  classical
  by_cases consistent : ∀ p q e, ¬ internal G support p e →
      ¬ internal G support q e → chi p e = chi q e
  · exact Or.inl (common_lifted_record G complete support origin chi alpha
      origin_mem odd record consistent)
  · right
    push Not at consistent
    obtain ⟨p, q, e, hp, hq, hd⟩ := consistent
    have root_closed : UnaryClosed out (fun x => internal G support x e) := by
      intro f x y hx hy
      exact ⟨support_mono f x y hy (G.left e) hx.1,
        support_mono f x y hy (G.right e) hx.2⟩
    refine ⟨e, ⟨closedCut_of_disagreement R out (fun x => internal G support x e)
      (fun x => chi x e) root_closed ?_ ?_ p q hp hq hd⟩⟩
    · intro f x y hy hx he
      exact unary_same f x y hy e hx he
    · intro n r x hx i j hi hj
      exact relation_same r x hx i j e hi hj

end GluingEPPA.Sparsening
