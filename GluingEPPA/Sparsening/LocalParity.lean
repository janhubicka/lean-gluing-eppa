import GluingEPPA.Parity

/-!
The local-cut obstruction used to unwind a chordless image cycle. This proves
path invariance and cancellation around a closed walk. Constructing the cut
from an arbitrary induced image cycle is a separate formalization obligation.
-/
namespace GluingEPPA.Sparsening
universe u v
variable {V : Type u} {E : Type v}
variable (G : EdgeGraph V E) [DecidableEq E] [Fintype E]

lemma double_zero (z : ZMod 2) : z + z = 0 := by
  calc
    z + z = (2 : ZMod 2) * z := by ring
    _ = 0 := by rw [EdgeGraph.two_zero]; simp

/-- Restrict a lifted walk to charts that contain one fixed ambient point. -/
def restrictedLift (allowed : V → Prop)
    (p q : V × (E → ZMod 2)) : Prop :=
  G.LiftEdge p q ∧ allowed p.1 ∧ allowed q.1

/-- One weight may be a different coboundary on different point supports. -/
theorem local_step_potential (allowed : V → Prop) (s : V → ZMod 2)
    (w : E → ZMod 2)
    (cut : ∀ e a b, G.Inc e a b → allowed a → allowed b → w e = s a + s b)
    {p q : V × (E → ZMod 2)} (h : restrictedLift G allowed p q) :
    s p.1 + EdgeGraph.dot w p.2 = s q.1 + EdgeGraph.dot w q.2 := by
  obtain ⟨⟨e, he, hq⟩, hp, ht⟩ := h
  rw [hq, EdgeGraph.dot_flip, cut e p.1 q.1 he hp ht]
  calc
    s p.1 + EdgeGraph.dot w p.2 =
        s p.1 + EdgeGraph.dot w p.2 + (s q.1 + s q.1) := by
      rw [double_zero, add_zero]
    _ = s q.1 + (EdgeGraph.dot w p.2 + (s p.1 + s q.1)) := by ring

theorem local_path_potential (allowed : V → Prop) (s : V → ZMod 2)
    (w : E → ZMod 2)
    (cut : ∀ e a b, G.Inc e a b → allowed a → allowed b → w e = s a + s b)
    {p q : V × (E → ZMod 2)}
    (h : Relation.ReflTransGen (restrictedLift G allowed) p q) :
    s p.1 + EdgeGraph.dot w p.2 = s q.1 + EdgeGraph.dot w q.2 := by
  induction h with
  | refl => rfl
  | tail _ e ih => exact ih.trans (local_step_potential G allowed s w cut e)

/-- Every interior potential occurs exactly twice. -/
theorem parity_telescopes (eta : Nat → ZMod 2) (n : Nat) :
    (∑ i ∈ Finset.range n, (eta i + eta (i+1))) = eta 0 + eta n := by
  induction n with
  | zero => simp [double_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    calc
      (eta 0 + eta n) + (eta n + eta (n+1)) =
          eta 0 + eta (n+1) + (eta n + eta n) := by ring
      _ = eta 0 + eta (n+1) := by rw [double_zero, add_zero]

/-- A closed walk cannot accumulate odd local-cut weight. -/
theorem closed_parity_sum_zero (eta w : Nat → ZMod 2) (n : Nat)
    (closed : eta n = eta 0)
    (edges : ∀ i < n, w i = eta i + eta (i+1)) :
    (∑ i ∈ Finset.range n, w i) = 0 := by
  calc
    (∑ i ∈ Finset.range n, w i) =
        ∑ i ∈ Finset.range n, (eta i + eta (i+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact edges i (Finset.mem_range.mp hi)
    _ = eta 0 + eta n := parity_telescopes eta n
    _ = 0 := by rw [closed, double_zero]

end GluingEPPA.Sparsening
