import GluingEPPA.Sparsening.OddBoundary

/-!
The no-separator branch constructs one *lifted* record, not just a common
base chart. Completeness of the graph on the support supplies edge chains;
a finite star sum corrects the boundary without changing exterior bits.
-/
namespace GluingEPPA.Sparsening
universe u v w
variable {V : Type u} {E : Type v} {P : Type w}
variable (G : GluingEPPA.EdgeGraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma boundary_add (a b : E → ZMod 2) (v : V) :
    boundary G (a + b) v = boundary G a v + boundary G b v := by
  simp only [boundary, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma boundary_scale (a : ZMod 2) (c : E → ZMod 2) (v : V) :
    boundary G (fun e => a * c e) v = a * boundary G c v := by
  simp only [boundary, mul_assoc, Finset.mul_sum]

lemma boundary_sum {T : Type*} [Fintype T] (c : T → E → ZMod 2) (v : V) :
    boundary G (fun e => ∑ t, c t e) v = ∑ t, boundary G (c t) v := by
  simp only [boundary, Finset.sum_mul]
  exact Finset.sum_comm

def edgeUnit (e : E) : E → ZMod 2 := fun d => if d = e then 1 else 0

/-- A single edge realizes the two endpoint charges. For equal endpoints
use zero, so no edge is required on a singleton vertex set. -/
theorem exists_edge_chain
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b) (a b : V) :
    ∃ c : E → ZMod 2,
      (∀ v, boundary G c v =
        (if a = v then 1 else 0) + (if b = v then 1 else 0)) ∧
      (∀ e, c e ≠ 0 → G.Inc e a b) := by
  classical
  by_cases hab : a = b
  · subst b
    refine ⟨0, ?_, ?_⟩
    · intro v
      simp [boundary, bit_add_self]
    · intro e he
      exact False.elim (he rfl)
  · obtain ⟨e, he⟩ := complete a b hab
    refine ⟨edgeUnit e, ?_, ?_⟩
    · intro v
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · simp [boundary, edgeUnit, ite_mul, ha, hb]
      · simp [boundary, edgeUnit, ite_mul, ha, hb, add_comm]
    · intro d hd
      have hde : d = e := by
        by_contra hn
        exact hd (by simp [edgeUnit, hn])
      subst d
      exact he

/-- An odd vertex vector supported on K differs from the point charge at
s in K by the boundary of an edge vector internal to K. -/
theorem internal_star_correction
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (K : V → Prop) (r : V → ZMod 2)
    (odd : (∑ v, r v) = 1) (supported : ∀ v, ¬ K v → r v = 0)
    (s : V) (hs : K s) :
    ∃ k : E → ZMod 2,
      (∀ v, boundary G k v = r v + (if s = v then 1 else 0)) ∧
      (∀ e, ¬ (K (G.left e) ∧ K (G.right e)) → k e = 0) := by
  classical
  choose c hb hi using (fun t : V => exists_edge_chain G complete s t)
  let k : E → ZMod 2 := fun e => ∑ t, r t * c t e
  refine ⟨k, ?_, ?_⟩
  · intro v
    change boundary G (fun e => ∑ t, r t * c t e) v = _
    rw [boundary_sum]
    simp_rw [boundary_scale, hb]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, odd]
    simp [mul_ite, add_comm]
  · intro e he
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : K t
    · have hc : c t e = 0 := by
        by_contra hne
        have inc := hi t e hne
        apply he
        rcases inc with ⟨hl, hr⟩ | ⟨hl, hr⟩
        · exact ⟨hl ▸ hs, hr ▸ ht⟩
        · exact ⟨hr ▸ ht, hl ▸ hs⟩
      rw [hc, mul_zero]
    · rw [supported t ht, zero_mul]

lemma boundary_eq_of_exterior
    (support : P → V → Prop) (p : P) (eta chi : E → ZMod 2)
    (agrees : ∀ e, ¬ internal G support p e → eta e = chi e)
    (v : V) (hv : ¬ support p v) : boundary G eta v = boundary G chi v := by
  classical
  unfold boundary
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : G.left e = v
  · rw [agrees e (fun h => hv (hl ▸ h.1))]
  · by_cases hr : G.right e = v
    · rw [agrees e (fun h => hv (hr ▸ h.2))]
    · simp [hl, hr]

/-- The simultaneous representative supplied in the no-separator case.
No quotient completeness or sparsening conclusion is assumed. -/
theorem common_lifted_record
    (complete : ∀ a b : V, a ≠ b → ∃ e, G.Inc e a b)
    (support : P → V → Prop) (origin : P → V)
    (chi : P → E → ZMod 2) (alpha : V → ZMod 2)
    (origin_mem : ∀ p, support p (origin p))
    (odd : (∑ v, alpha v) = 1)
    (record : ∀ p v,
      boundary G (chi p) v + (if origin p = v then 1 else 0) = alpha v)
    (consistent : ∀ p q e, ¬ internal G support p e →
      ¬ internal G support q e → chi p e = chi q e) :
    ∃ s c, (∀ p, support p s) ∧
      (∀ p e, ¬ internal G support p e → c e = chi p e) ∧
      (∀ v, boundary G c v + (if s = v then 1 else 0) = alpha v) := by
  classical
  obtain ⟨eta, hext⟩ := exterior_completion G support chi consistent
  obtain ⟨s, hs⟩ := common_chart_of_consistent_records G support origin chi alpha
    origin_mem odd record consistent
  let K : V → Prop := fun v => ∀ p, support p v
  let r : V → ZMod 2 := fun v => alpha v + boundary G eta v
  have hrOdd : (∑ v, r v) = 1 := by
    simp only [r, Finset.sum_add_distrib, odd, sum_boundary, add_zero]
  have hrSupp : ∀ v, ¬ K v → r v = 0 := by
    intro v hmissing
    have hp : ∃ p, ¬ support p v := by
      by_contra hn
      apply hmissing
      intro p
      by_contra h
      exact hn ⟨p, h⟩
    obtain ⟨p, hp⟩ := hp
    have horigin : origin p ≠ v := fun h => hp (h ▸ origin_mem p)
    have hb : boundary G eta v = alpha v := by
      rw [boundary_eq_of_exterior G support p eta (chi p) (hext p) v hp]
      simpa [horigin] using record p v
    dsimp [r]
    rw [hb, bit_add_self]
  obtain ⟨k, hk, hke⟩ := internal_star_correction G complete K r hrOdd hrSupp s hs
  refine ⟨s, eta + k, hs, ?_, ?_⟩
  · intro p e he
    have hout : ¬ (K (G.left e) ∧ K (G.right e)) :=
      fun h => he ⟨h.1 p, h.2 p⟩
    change eta e + k e = chi p e
    rw [hke e hout, add_zero, hext p e he]
  · intro v
    rw [boundary_add, hk]
    dsimp [r]
    calc
      boundary G eta v + (alpha v + boundary G eta v +
          (if s = v then 1 else 0)) + (if s = v then 1 else 0) =
        alpha v + (boundary G eta v + boundary G eta v) +
          ((if s = v then 1 else 0) + (if s = v then 1 else 0)) := by abel
      _ = alpha v := by rw [bit_add_self, bit_add_self, add_zero, add_zero]

end GluingEPPA.Sparsening
