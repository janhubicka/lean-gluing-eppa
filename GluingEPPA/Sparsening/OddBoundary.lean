import GluingEPPA.Sparsening.LocalParity

/-!
Boundary/exterior records for complete-overlap refinement. These lemmas
prove common *base-chart* support from consistent exterior records.
A common lifted chart additionally needs the star correction and record
completeness; neither is hidden as an assumption here.
-/
namespace GluingEPPA.Sparsening
universe u v w

lemma bit_add_self (a : ZMod 2) : a + a = 0 := double_zero a

variable {V : Type u} {E : Type v} {P : Type w}
variable (G : GluingEPPA.EdgeGraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V]

/-- Count both endpoints; even a loop has zero total boundary. -/
def boundary (c : E → ZMod 2) (v : V) : ZMod 2 :=
  ∑ e, c e * ((if G.left e = v then 1 else 0) +
    (if G.right e = v then 1 else 0))

lemma sum_boundary (c : E → ZMod 2) :
    (∑ v, boundary G c v) = 0 := by
  classical
  unfold boundary
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.mul_sum]
  have hunit (a : V) :
      (∑ v : V, if a = v then (1 : ZMod 2) else 0) = 1 := by
    simp
  have hend : (∑ v : V,
      ((if G.left e = v then (1 : ZMod 2) else 0) +
       (if G.right e = v then (1 : ZMod 2) else 0))) = 0 := by
    rw [Finset.sum_add_distrib, hunit, hunit]
    exact bit_add_self 1
  rw [hend, mul_zero]

/-- An odd record cannot agree everywhere with a boundary. -/
theorem common_chart_of_boundary
    (support : P → V → Prop) (alpha : V → ZMod 2) (c : E → ZMod 2)
    (odd : (∑ v, alpha v) = 1)
    (outside : ∀ v, (∃ p, ¬ support p v) → boundary G c v = alpha v) :
    ∃ v, ∀ p, support p v := by
  classical
  by_contra h
  have missing (v : V) : ∃ p, ¬ support p v := by
    by_contra hm
    apply h
    refine ⟨v, ?_⟩
    intro p
    by_contra hp
    exact hm ⟨p, hp⟩
  have heq : boundary G c = alpha := funext (fun v => outside v (missing v))
  have hz : (∑ v, alpha v) = 0 := by
    rw [← heq]
    exact sum_boundary G c
  exact zero_ne_one (hz.symm.trans odd)

/-- An edge is internal to a point when both endpoints contain the point. -/
def internal (support : P → V → Prop) (p : P) (e : E) : Prop :=
  support p (G.left e) ∧ support p (G.right e)

/-- Compatible partial exterior records extend to one total valuation. -/
theorem exterior_completion
    (support : P → V → Prop) (chi : P → E → ZMod 2)
    (consistent : ∀ p q e, ¬ internal G support p e →
      ¬ internal G support q e → chi p e = chi q e) :
    ∃ eta : E → ZMod 2,
      ∀ p e, ¬ internal G support p e → eta e = chi p e := by
  classical
  let eta : E → ZMod 2 := fun e =>
    if h : ∃ p, ¬ internal G support p e then chi (Classical.choose h) e else 0
  refine ⟨eta, ?_⟩
  intro p e hp
  have he : ∃ q, ¬ internal G support q e := ⟨p, hp⟩
  dsimp only [eta]
  rw [dif_pos he]
  exact consistent (Classical.choose he) p e (Classical.choose_spec he) hp

/-- Common base support, not yet a common representative in a lifted chart. -/
theorem common_chart_of_consistent_records
    (support : P → V → Prop) (origin : P → V)
    (chi : P → E → ZMod 2) (alpha : V → ZMod 2)
    (origin_mem : ∀ p, support p (origin p))
    (odd : (∑ v, alpha v) = 1)
    (record : ∀ p v,
      boundary G (chi p) v + (if origin p = v then 1 else 0) = alpha v)
    (consistent : ∀ p q e, ¬ internal G support p e →
      ¬ internal G support q e → chi p e = chi q e) :
    ∃ v, ∀ p, support p v := by
  classical
  obtain ⟨eta, hext⟩ := exterior_completion G support chi consistent
  apply common_chart_of_boundary G support alpha eta odd
  intro v hmissing
  obtain ⟨p, hp⟩ := hmissing
  have horigin : origin p ≠ v := by
    intro h
    exact hp (h ▸ origin_mem p)
  have hboundary : boundary G eta v = boundary G (chi p) v := by
    unfold boundary
    apply Finset.sum_congr rfl
    intro e _
    by_cases hl : G.left e = v
    · have he : ¬ internal G support p e := by
        intro hi
        exact hp (hl ▸ hi.1)
      rw [hext p e he]
    · by_cases hr : G.right e = v
      · have he : ¬ internal G support p e := by
          intro hi
          exact hp (hr ▸ hi.2)
        rw [hext p e he]
      · simp [hl, hr]
  rw [hboundary]
  simpa [horigin] using record p v

end GluingEPPA.Sparsening
