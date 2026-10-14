import GluingEPPA.Basic

/-!
Finite descent for sparsening. Vertex identifications and edge gains are both
counted: merely claiming that graph girth increases would miss rectangles.
These numerical lemmas do not assume or assert the geometric step theorem.
-/
namespace GluingEPPA.Sparsening

/-- A convenient rectangular rank; the manuscript also gives a tighter cubic
count by summing the possible edge counts at each vertex cardinality. -/
def rank (M m e : Nat) : Int := (m : Int) * ((M : Int) + 1) - (e : Int)

theorem rank_nonnegative {M m e : Nat} (hm : 1 ≤ m) (he : e ≤ M) :
    0 ≤ rank M m e := by
  have hm' : (1 : Int) ≤ m := by exact_mod_cast hm
  have he' : (e : Int) ≤ M := by exact_mod_cast he
  have hM : (0 : Int) ≤ M := by positivity
  have hmul := mul_le_mul_of_nonneg_right hm' (show (0 : Int) ≤ (M : Int)+1 by omega)
  dsimp [rank]
  nlinarith

/-- A smaller image, or the same image size with an extra edge, lowers rank. -/
theorem rank_decreases {M m m' e e' : Nat}
    (he : e ≤ M) (he' : e' ≤ M)
    (step : m' < m ∨ (m' = m ∧ e < e')) :
    rank M m' e' < rank M m e := by
  have hM : (0 : Int) ≤ M := by positivity
  have he0 : (0 : Int) ≤ e := by positivity
  have he'0 : (0 : Int) ≤ e' := by positivity
  have heM : (e : Int) ≤ M := by exact_mod_cast he
  have he'M : (e' : Int) ≤ M := by exact_mod_cast he'
  dsimp [rank]
  rcases step with hm | ⟨rfl, hee⟩
  · have hmNat : m' + 1 ≤ m := by omega
    have hm' : (m' : Int) + 1 ≤ m := by exact_mod_cast hmNat
    have hmul := mul_le_mul_of_nonneg_right hm' (show (0 : Int) ≤ (M : Int)+1 by omega)
    nlinarith
  · have hee' : (e : Int) < e' := by exact_mod_cast hee
    omega

theorem strict_chain_bound (r : Nat → Int) (n : Nat)
    (step : ∀ i < n, r (i+1) < r i) : r n + (n : Int) ≤ r 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprefix : ∀ i < n, r (i+1) < r i := fun i hi => step i (by omega)
    have hprev := ih hprefix
    have hlast := step n (by omega)
    push_cast
    omega

/-- A nonnegative bounded rank cannot decrease at every bad stage. -/
theorem exists_good_stage (r : Nat → Int) (good : Nat → Prop) (n : Nat)
    (lower : ∀ i ≤ n, 0 ≤ r i) (upper : r 0 < n)
    (step : ∀ i < n, ¬ good i → r (i+1) < r i) :
    ∃ i ≤ n, good i := by
  classical
  by_contra h
  have hnot : ∀ i ≤ n, ¬ good i := by
    intro i hi hg
    exact h ⟨i, hi, hg⟩
  have hbound := strict_chain_bound r n (fun i hi => step i hi (hnot i (by omega)))
  have hlow := lower n (by omega)
  omega

end GluingEPPA.Sparsening
