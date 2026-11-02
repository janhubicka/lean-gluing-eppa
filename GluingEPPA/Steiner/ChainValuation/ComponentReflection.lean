import GluingEPPA.Steiner.ChainValuation.ComponentImage
import GluingEPPA.Steiner.ChainValuation.ReflectionWitness

/-!
# Reflection of coset intersections in the literal gluing lift

Unlike ReflectionWitness, this file does not assume that the carrying walk
or a suitable component representative has already been found. It extracts
them from the actual C_B action and its invariant image.

The exact construction inputs remain explicit: the earlier-group inclusion,
word generation, equality of the recorded component permutations when full
word values agree, and endpoint repair. The augmented finite recursion must
supply these inputs. No acyclicity or reflection hypothesis is assumed.
-/

namespace GluingEPPA.Steiner
namespace EdgeGraph

universe u v w z
variable {V : Type u} {E : Type v} {G : Type w} {H : Type z}
variable [Group G] [Group H]
variable (D : EdgeGraph V E) (edgeValue : E → G)
variable (B : Set E) (b : E → H) (hb : ∀ e ∈ B, b e * b e = 1)
variable (i : H →* G) (hi : ∀ e ∈ B, i (b e) = edgeValue e)

/-- The normalized forward implication, including extraction of its actual walk. -/
theorem chain_reflection_from_records
    (hinv : ∀ e, edgeValue e * edgeValue e = 1)
    {A : Set E} (KA : Subgroup G)
    (hgenA : ∀ e ∈ A, edgeValue e ∈ KA)
    (hwordsA : ∀ a ∈ KA, ∃ w : List E,
      (∀ e ∈ w, e ∈ A) ∧ (w.map edgeValue).prod = a)
    (hwordsB : ∀ k : H, ∃ w : List E,
      (∀ e ∈ w, e ∈ B) ∧ (w.map b).prod = k)
    (hrecord : ∀ p q : List E,
      (p.map edgeValue).prod = (q.map edgeValue).prod →
        D.componentWordPerm B b hb p = D.componentWordPerm B b hb q)
    (hrepair : ∀ (s t : V) (k : G),
      D.WalkValue Set.univ edgeValue s t k → k ∈ KA →
        D.WalkValue A edgeValue s t k)
    {s t : V} {h a : G} {beta : H}
    (p : D.WalkValue Set.univ edgeValue s t h)
    (ha : a ∈ KA) (hab : a = h * i beta) :
    (D.componentSet A edgeValue (s, 1) ∩
      D.componentSet B edgeValue (t, h)).Nonempty := by
  obtain ⟨wa, hwa, hva⟩ := hwordsA a ha
  obtain ⟨wb, hwb, hvb⟩ := hwordsB beta
  obtain ⟨wp, hwp, hvp⟩ :=
    WalkValue.exists_word (D := D) (a := edgeValue) p
  have hvb' : (wb.map edgeValue).prod = i beta := by
    rw [← D.chain_word_map_value B b hb edgeValue i hi wb hwb, hvb]
  have hval : ((wp ++ wb).map edgeValue).prod = (wa.map edgeValue).prod := by
    simp only [List.map_append, List.prod_append, hvp, hvb', hva]
    exact hab.symm
  have heq := hrecord (wp ++ wb) wa hval
  have haction :
      D.componentWordPerm B b hb wa (D.component B b hb s 1) =
        D.component B b hb t beta⁻¹ := by
    rw [← heq, D.componentWordPerm_append,
      D.componentWordPerm_walk B b hb hwp,
      D.chain_componentWord_internal B b hb wb hwb t 1,
      hvb, mul_one]
  have hgenImage : ∀ e ∈ A, e ∈ B → b e ∈ KA.comap i := by
    intro e he heB
    change i (b e) ∈ KA
    rw [hi e heB]
    exact hgenA e he
  have hmem := D.chainComponentImage_word B b hb (KA.comap i)
    hgenImage wa hwa (D.chainComponentImage_distinguished B b hb (KA.comap i) s)
  rw [haction] at hmem
  obtain ⟨v, q, hq, hc⟩ := hmem
  have rH : D.WalkValue B b v t (q⁻¹ * beta⁻¹) :=
    (D.component_eq_iff_value B b hb v t q beta⁻¹).1 hc
  have rG : D.WalkValue B edgeValue v t ((i q)⁻¹ * (i beta)⁻¹) := by
    have mapped := (rH.map i).congr_edges hi
    simpa only [map_mul, map_inv] using mapped
  have hwitness := D.chain_reflection_witness edgeValue hinv KA hrepair
    p ha (show i q ∈ KA from hq) hab rG
  exact ⟨(v, a * i q), hwitness⟩

/-- Reflection for arbitrary anchors in one full lifted component.

The second abstract subgroup is the range of the earlier-group inclusion.
Every action, walk, component and coset in the conclusion is an existing
concrete definition. Word generation and record compatibility are inputs to
be instantiated by the augmented recursive construction, not new axioms.
-/
theorem chain_coset_component_reflection
    (hinv : ∀ e, edgeValue e * edgeValue e = 1)
    {A : Set E} (KA : Subgroup G)
    (hgenA : ∀ e ∈ A, edgeValue e ∈ KA)
    (hwordsA : ∀ a ∈ KA, ∃ w : List E,
      (∀ e ∈ w, e ∈ A) ∧ (w.map edgeValue).prod = a)
    (hwordsB : ∀ k : H, ∃ w : List E,
      (∀ e ∈ w, e ∈ B) ∧ (w.map b).prod = k)
    (hrecord : ∀ p q : List E,
      (p.map edgeValue).prod = (q.map edgeValue).prod →
        D.componentWordPerm B b hb p = D.componentWordPerm B b hb q)
    (hrepair : ∀ (s t : V) (k : G),
      D.WalkValue Set.univ edgeValue s t k → k ∈ KA →
        D.WalkValue A edgeValue s t k)
    {s t : V} {g h : G}
    (hconnected : D.CayleyWalk Set.univ edgeValue s g t h) :
    (ChainValuation.leftCoset KA g ∩ ChainValuation.leftCoset i.range h).Nonempty ↔
      (D.componentSet A edgeValue (s, g) ∩
        D.componentSet B edgeValue (t, h)).Nonempty := by
  constructor
  · rintro ⟨x, hxA, hxB⟩
    change g⁻¹ * x ∈ KA at hxA
    change h⁻¹ * x ∈ i.range at hxB
    obtain ⟨beta, hbeta⟩ := hxB
    have hab : g⁻¹ * x = (g⁻¹ * h) * i beta := by
      rw [hbeta]
      group
    obtain ⟨⟨v, k⟩, hvA, hvB⟩ :=
      D.chain_reflection_from_records edgeValue B b hb i hi hinv KA
        hgenA hwordsA hwordsB hrecord hrepair hconnected.value hxA hab
    refine ⟨(v, g * k), ?_, ?_⟩
    · change D.CayleyWalk A edgeValue s g v (g * k)
      have lifted := (D.cayleyWalk_left_mul A edgeValue g s v 1 k).2 hvA
      simpa only [mul_one] using lifted
    · change D.CayleyWalk B edgeValue t h v (g * k)
      have lifted :=
        (D.cayleyWalk_left_mul B edgeValue g t v (g⁻¹ * h) k).2 hvB
      simpa only [mul_inv_cancel_left] using lifted
  · rintro ⟨⟨v, k⟩, hvA, hvB⟩
    refine ⟨k, ?_, ?_⟩
    · change g⁻¹ * k ∈ KA
      exact D.chain_walkValue_mem edgeValue KA hgenA
        ((D.mem_componentSet_iff A edgeValue s v g k).1 hvA)
    · change h⁻¹ * k ∈ i.range
      apply D.chain_walkValue_mem edgeValue i.range
        (fun e he => ⟨b e, hi e he⟩)
      exact (D.mem_componentSet_iff B edgeValue t v h k).1 hvB

end EdgeGraph
end GluingEPPA.Steiner
