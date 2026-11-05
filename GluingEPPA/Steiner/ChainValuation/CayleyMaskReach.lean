import GluingEPPA.Steiner.ChainValuation.ChainAttachReach
import GluingEPPA.Steiner.ChainValuation.Cosets

/-!
# Masked Cayley reachability is a subgroup coset

For a finite Cayley block with named involutive generators, connectivity
using only colours in M is exactly a left coset of the subgroup generated
by those permitted generator values. The formulation below uses an
explicit subgroup P, together with both directions of its word
generation property. It is valid for arbitrary, possibly nonabelian,
block groups.

The next stage specializes P to the range of the earlier Link inclusion
for M ∩ A. That is the missing input to the two-group attachment
pullback argument, not an arbitrary N-acyclicity assumption.
-/

namespace GluingEPPA.Steiner.ChainValuation

universe u v
variable {E : Type u}

/-- A word using only active letters of M is a path in the original
named Cayley-edge relation. Missing colours contribute no edges. -/
theorem cayley_mask_word_reach
    (B : GroupBlock.{u,v} E) (M : Finset E) (w : List E)
    (hw : ∀ e ∈ w, e ∈ M ∧ e ∈ B.active)
    (x : B.Carrier) :
    LabelReach (fun e => (B.matching e).Rel) M
      x (x * (w.map B.edge).prod) := by
  induction w generalizing x with
  | nil =>
      simpa using
        (LabelReach.refl x :
          LabelReach (fun e => (B.matching e).Rel) M x x)
  | cons e es ih =>
      have he : e ∈ M := (hw e (by simp)).1
      have hb : e ∈ B.active := (hw e (by simp)).2
      have htail : ∀ a ∈ es, a ∈ M ∧ a ∈ B.active := by
        intro a ha
        exact hw a (by simp [ha])
      have hfirst : LabelReach (fun a => (B.matching a).Rel) M
          x (x * B.edge e) :=
        LabelReach.edge e he (B.matching_rel hb x)
      have hrest := ih htail (x * B.edge e)
      have hpath := LabelReach.trans hfirst hrest
      simpa only [List.map_cons, List.prod_cons, mul_assoc] using hpath

/-- Every M-coloured Cayley path stays within a left coset of any subgroup
containing all active named M-generators. -/
theorem cayley_mask_reach_subgroup
    (B : GroupBlock.{u,v} E) (M : Finset E)
    (P : Subgroup B.Carrier)
    (hgen : ∀ e, e ∈ M → e ∈ B.active → B.edge e ∈ P)
    {x y : B.Carrier}
    (h : LabelReach (fun e => (B.matching e).Rel) M x y) :
    x⁻¹ * y ∈ P := by
  induction h with
  | refl x =>
      simpa using (P.one_mem : (1 : B.Carrier) ∈ P)
  | edge e he hxy =>
      change e ∈ B.active ∧ _ at hxy
      obtain ⟨hb, heq⟩ := hxy
      rw [heq]
      convert hgen e he hb using 1 <;> group
  | symm h ih =>
      convert P.inv_mem ih using 1 <;> group
  | trans h k ih ik =>
      convert P.mul_mem ih ik using 1 <;> group

/-- The full coset description, assuming every element of P has a word
representative using the genuinely active M-letters. This characterizes
all actual M-components and not merely a bound on their size. -/
theorem cayley_mask_reach_iff_coset
    (B : GroupBlock.{u,v} E) (M : Finset E)
    (P : Subgroup B.Carrier)
    (hgen : ∀ e, e ∈ M → e ∈ B.active → B.edge e ∈ P)
    (hwords : ∀ p : B.Carrier, p ∈ P →
      ∃ w : List E,
        (∀ e ∈ w, e ∈ M ∧ e ∈ B.active) ∧
        (w.map B.edge).prod = p)
    (x y : B.Carrier) :
    LabelReach (fun e => (B.matching e).Rel) M x y ↔
      y ∈ leftCoset P x := by
  constructor
  · intro h
    exact cayley_mask_reach_subgroup B M P hgen h
  · intro h
    change x⁻¹ * y ∈ P at h
    obtain ⟨w, hw, hval⟩ := hwords (x⁻¹ * y) h
    have hp := cayley_mask_word_reach B M w hw x
    have hy : x * (w.map B.edge).prod = y := by
      rw [hval]
      group
    rw [← hy]
    exact hp

end GluingEPPA.Steiner.ChainValuation
